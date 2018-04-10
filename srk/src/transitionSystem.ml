open BatPervasives
open Syntax

include Log.Make(struct let name = "srk.transitionSystem" end)

module WG = WeightedGraph
module Int = SrkUtil.Int

type 'a label = 'a WeightedGraph.label =
  | Weight of 'a
  | Call of int * int
[@@deriving ord]

module Make
    (C : sig
       type t
       val context : t context
     end)
    (Var : sig
       type t
       val pp : Format.formatter -> t -> unit
       val typ : t -> [ `TyInt | `TyReal ]
       val compare : t -> t -> int
       val symbol_of : t -> symbol
       val of_symbol : symbol -> t option
       val is_global : t -> bool
       val hash : t -> int
       val equal : t -> t -> bool
     end)
    (T : sig
       type t
       type var = Var.t
       val pp : Format.formatter -> t -> unit
       val guard : t -> C.t formula
       val transform : t -> (var * C.t term) BatEnum.t
       val mem_transform : var -> t -> bool
       val get_transform : var -> t -> C.t term
       val assume : C.t formula -> t
       val compare : t -> t -> int
       val equal : t -> t -> bool
       val mul : t -> t -> t
       val add : t -> t -> t
       val zero : t
       val one : t
       val star : t -> t
       val widen : t -> t -> t
       val exists : (var -> bool) -> t -> t
     end)
= struct

  type vertex = int
  type transition = T.t
  type tlabel = T.t label [@@deriving ord]

  include WeightedGraph.MakeRecGraph(struct
      include T
      let project = exists Var.is_global
    end)
      
  (* Weight-labeled graph module suitable for ocamlgraph *)
  module WGG = struct
    type t = T.t label WG.t

    module V = struct
      include SrkUtil.Int
      type label = int
      let label x = x
      let create x = x
    end

    module E = struct
      type label = tlabel
      type vertex = int
      type t = int * tlabel * int [@@deriving ord]
      let src (x, _, _) = x
      let dst (_, _, x) = x
      let label (_, x, _) = x
      let create x y z = (x, y, z)
    end

    let iter_edges_e = WG.iter_edges
    let iter_vertex = WG.iter_vertex
    let iter_succ f tg v =
      WG.U.iter_succ f (WG.forget_weights tg) v
    let fold_pred_e = WG.fold_pred_e
  end

  module Wto = Graph.WeakTopological.Make(WGG)
  module VarMap = BatMap.Make(Var)
  module VarSet = BatSet.Make(Var)

  let srk = C.context

  let defines tr =
    BatEnum.fold
      (fun defs (var, _) -> VarSet.add var defs)
      VarSet.empty
      (T.transform tr)

  let uses tr =
    BatEnum.fold
      (fun uses (_, term) ->
         Symbol.Set.union (symbols term) uses)
      (symbols (T.guard tr))
      (T.transform tr)
    |> Symbol.Set.enum
    |> BatEnum.filter_map Var.of_symbol
    |> BatList.of_enum

  let references tr =
    let add_symbols =
      Symbol.Set.fold (fun s vars ->
          match Var.of_symbol s with
          | Some v -> VarSet.add v vars
          | None -> vars)
    in
    BatEnum.fold
      (fun refs (var, term) -> add_symbols (symbols term) (VarSet.add var refs))
      (add_symbols (symbols (T.guard tr)) VarSet.empty)
      (T.transform tr)

  (* Interval abstract domain *)
  module Box = struct

    (* Variables not belonging to an interval store are implicitly mapped to
       top *)
    type t =
      | Store of Interval.t VarMap.t
      | Bottom
    [@@deriving ord]

    type edge = int * tlabel * int

    let pp formatter prop =
      let open Format in
      let pp_elt formatter (v, ivl) =
        fprintf formatter "@[%a -> %a@]" Var.pp v Interval.pp ivl
      in
      match prop with
      | Bottom -> fprintf formatter "Bottom"
      | Store s when VarMap.is_empty s -> fprintf formatter "Top"
      | Store s -> SrkUtil.pp_print_enum pp_elt formatter (VarMap.enum s)

    let equal x y = match x, y with
      | Store x, Store y -> VarMap.equal Interval.equal x y
      | Bottom, Bottom -> true
      | _, _ -> false

    let bottom = Bottom
    let top = Store VarMap.empty

    let widening x y =
      let widening _ x y = match x, y with
        | Some x, Some y ->
          let result = Interval.widening x y in
          if Interval.equal result Interval.top then
            None
          else
            Some result
        | _, _ -> None
      in
      match x, y with
      | Bottom, x | x, Bottom -> x
      | Store x, Store y -> Store (VarMap.merge widening x y)

    let join x y =
      let join _ x y = match x, y with
        | Some x, Some y -> Some (Interval.join x y)
        | _, _ -> None
      in
      match x, y with
      | Bottom, x | x, Bottom -> x
      | Store x, Store y -> Store (VarMap.merge join x y)

    let is_local s =
      match Var.of_symbol s with
      | None -> true
      | Some v -> not (Var.is_global v)

    let to_formula store =
      let boxes = ref [] in
      store |> VarMap.iter (fun v ivl ->
          let t = mk_const srk (Var.symbol_of v) in
          begin match Interval.lower ivl with
            | Some lo -> boxes := (mk_leq srk (mk_real srk lo) t)::(!boxes)
            | None -> ()
          end;
          begin match Interval.upper ivl with
            | Some hi -> boxes := (mk_leq srk t (mk_real srk hi))::(!boxes)
            | None -> ()
          end);
      mk_and srk (!boxes)

    let analyze (_s, label, t) prop =
      match prop, label with
      | Bottom, _ -> Bottom
      | Store store, Call (_, _) ->
        Store (VarMap.filter
                 (fun v _ -> not (Var.is_global v))
                 store)
      | Store store, Weight tr ->
        logf ~level:`trace "In: %a" pp prop;
        logf ~level:`trace "Transition: %a" T.pp tr;
        let guards = ref [T.guard tr] in
        let push_guard x = guards := x::(!guards) in
        uses tr |> List.iter (fun v ->
            if VarMap.mem v store then
              let ivl = VarMap.find v store in
              let t = mk_const srk (Var.symbol_of v) in
              begin match Interval.lower ivl with
                | Some lo -> push_guard (mk_leq srk (mk_real srk lo) t)
                | None -> ()
              end;
              begin match Interval.upper ivl with
                | Some hi -> push_guard (mk_leq srk t (mk_real srk hi))
                | None -> ()
              end);
        let guard = mk_and srk (!guards) in
        (* variables used/defined by tr *)
        let vars = VarSet.elements (references tr) in
        let objectives =
          List.map (fun v ->
              if T.mem_transform v tr then
                T.get_transform v tr
              else
                mk_const srk (Var.symbol_of v))
            vars
        in
        let result =
          match Nonlinear.optimize_box srk guard objectives with
          | `Sat intervals ->
            let store' =
              List.fold_left2
                (fun m v ivl ->
                   if Interval.equal ivl Interval.top then
                     VarMap.remove v m
                   else
                     VarMap.add v ivl m)
                store
                vars
                intervals
            in
            Store store'
          | `Unsat -> Bottom
          | `Unknown ->
            Store (BatEnum.fold
                     (fun m (v, _) -> VarMap.remove v m)
                     store
                     (T.transform tr))
        in
        logf ~level:`trace "Out: %a" pp result;
        result
  end
  module IntervalAnalysis = Graph.ChaoticIteration.Make(WGG)(Box)
  module IntPair = struct
    type t = int * int [@@deriving ord]
    let equal (x,y) (x',y') = (x=x' && y=y')
    let hash = Hashtbl.hash
  end

  module PS = BatSet.Make(IntPair)
  module PHT = BatHashtbl.Make(IntPair)
  module VHT = BatHashtbl.Make(Var)

  (* Remove temporary variables that are referenced by only one transition *)
  let remove_temporaries tg =
    (* Map each local variable to the set of transitions that refer to it *)
    let ref_map = VHT.create 991 in
    let add_ref var (u, v) =
      if not (Var.is_global var) then
        VHT.modify_def PS.empty var (PS.add (u,v)) ref_map
    in
    tg |> WG.iter_edges (fun (u, label, v) ->
        match label with
        | Call _ -> ()
        | Weight tr ->
          VarSet.iter (fun var -> add_ref var (u, v)) (references tr));

    (* Map each transition to its temporary variables not referenced by any
       other transition *)
    let tmp_map = PHT.create 991 in
    let add_tmp (u, v) var =
      PHT.modify_def VarSet.empty (u,v) (VarSet.add var) tmp_map
    in
    ref_map |> VHT.iter (fun var ps ->
        if PS.cardinal ps = 1 then
          add_tmp (PS.choose ps) var);
    tg |> WG.map_weights (fun u label v ->
        match label with
        | Call _ -> label
        | Weight tr ->
          try
            let tmp = PHT.find tmp_map (u, v) in
            Weight (T.exists (fun x -> not (VarSet.mem x tmp)) tr)
          with Not_found -> label)

  let forward_invariants tg entry  =
    let wto = Wto.recursive_scc tg entry in
    let init v =
      if v = entry then Box.top
      else Box.bottom
    in
    let result =
      IntervalAnalysis.recurse tg wto init Graph.ChaoticIteration.FromWto 3
    in
    let rec loop_vertices vertices wto =
      let open Graph.WeakTopological in
      match wto with
      | Vertex v -> Int.Set.add v vertices
      | Component (v, rest) ->
        fold_left loop_vertices (Int.Set.add v vertices) rest
    in
    let loop_references wto =
      let vertices = loop_vertices Int.Set.empty wto in
      Int.Set.fold (fun u vars ->
          WG.fold_succ_e (fun (_, weight, v) vars ->
              match weight with
              | Weight tr when Int.Set.mem v vertices ->
                VarSet.union vars (references tr)
              | _ -> vars)
            tg
            u
            vars)
        vertices
        VarSet.empty
    in
    let rec invariants inv wto =
      let open Graph.WeakTopological in
      match wto with
      | Vertex v -> inv
      | Component (v, rest) ->
        let invariant =
          match IntervalAnalysis.M.find v result with
          | Box.Bottom -> mk_false srk
          | Box.Store store -> 
            VarSet.fold (fun v inv ->
                if VarMap.mem v store then
                  VarMap.add v (VarMap.find v store) inv
                else
                  inv)
              (loop_references wto)
              VarMap.empty
            |> Box.to_formula
        in
        logf "Found invariant at %d: %a"
          v
          (Formula.pp srk) invariant;
        fold_left invariants ((v,invariant)::inv) rest
    in
    Graph.WeakTopological.fold_left invariants [] wto

  let simplify p tg =
    let rec go tg =
      let continue = ref false in
      let tg' =
        WG.fold_vertex (fun v tg ->
            let ug = WG.forget_weights tg in
            if (p v
                || WG.mem_edge tg v v
                || WG.U.in_degree ug v != 1
                || WG.U.out_degree ug v != 1) then
              tg
            else begin
              try
                let tg = WG.contract_vertex tg v in
                continue := true;
                tg
              with _ -> tg
            end)
          tg
          tg
      in
      if !continue then go tg'
      else tg'
    in
    go tg
end
