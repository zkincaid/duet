open BatPervasives
open Syntax

include Log.Make(struct let name = "srk.transitionSystem" end)

module WG = WeightedGraph
module Int = SrkUtil.Int
module ISet = BatSet.Make(Int)

type 'a label =
  | Weight of 'a
  | Call of int * int


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
       val transform : t -> (var * C.t arith_term) BatEnum.t
       val mem_transform : var -> t -> bool
       val get_transform : var -> t -> C.t arith_term
       val assume : C.t formula -> t
       val mul : t -> t -> t
       val add : t -> t -> t
       val zero : t
       val one : t
       val star : t -> t
       val exists : (var -> bool) -> t -> t
       val try_rtc : t -> t option
     end)
= struct

  type vertex = int
  type transition = T.t
  type tlabel = T.t label

  type query = T.t WG.RecGraph.weight_query
  type reverse_query = T.t WG.RecGraph.reverse_query

  let mk_query ?(delay=1) ts source dom =
    let rg =
      WG.fold_vertex
        (fun v rg -> WG.RecGraph.add_vertex rg v)
        ts
        (WG.RecGraph.empty ())
      |> WG.fold_edges (fun (u, w, v) rg ->
             match w with
             | Call (en,ex) ->
                WG.RecGraph.add_call_edge rg u (en,ex) v
             | Weight _ -> WG.RecGraph.add_edge rg u v)
           ts
    in
    let algebra = function
      | `Edge (u,v) ->
         begin match WG.edge_weight ts u v with
         | Weight w -> w
         | Call _ -> assert false
         end
      | `Add (x, y) -> T.add x y
      | `Mul (x, y) -> T.mul x y
      | `Star x -> T.star x
      | `Segment x -> T.exists Var.is_global x
      | `Zero -> T.zero
      | `One -> T.one
    in
    WG.RecGraph.summarize_iterative
      (WG.RecGraph.mk_query rg source)
      algebra
      ~delay
      dom

  type t = (T.t label) WG.t

  let path_weight = WG.RecGraph.path_weight
  let call_weight = WG.RecGraph.call_weight
  let omega_path_weight = WG.RecGraph.omega_path_weight

  let label_algebra =
    let add x y = match x, y with
      | Weight x, Weight y -> Weight (T.add x y)
      | _, _ -> invalid_arg "No weight operations for call edges" in
    let mul x y = match x, y with
      | Weight x, Weight y -> Weight (T.mul x y)
      | _, _ -> invalid_arg "No weight operations for call edges" in
    let star = function
      | Weight x -> Weight (T.star x)
      | _ -> invalid_arg "No weight operations for call edges" in
    let zero = Weight T.zero in
    let one = Weight T.one in
    WG.{ add; mul; star; zero; one }

  let empty = WG.empty label_algebra

  (* Weight-labeled graph module suitable for ocamlgraph *)
  module WGG = struct
    type t = T.t label WG.t

    module V = SrkUtil.Int

    module E = struct
      type t = int * tlabel * int
      let src (x, _, _) = x
    end

    let iter_vertex = WG.iter_vertex
    let iter_succ f tg v =
      WG.U.iter_succ f (WG.forget_weights tg) v
    let fold_pred_e = WG.fold_pred_e
  end

  module L = Loop.Make(WGG)
  module VarMap = BatMap.Make(Var)
  module VarSet = BatSet.Make(Var)

  let srk = C.context

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


  let set_summary q (u, v) summary = 
    WG.RecGraph.set_summary q (u, v) summary
  
  let get_summary q (u, v) = 
    WG.RecGraph.get_summary q (u, v)
    
  let mk_reverse_query = WG.RecGraph.mk_reverse_query
  let exit_summary = WG.RecGraph.exit_summary
  let target_summary = WG.RecGraph.target_summary

  (* Variables whose abstract values may change as the result of a
     transition *)
  let abstract_defs tr =
    let add_symbols =
      Symbol.Set.fold (fun s vars ->
          match Var.of_symbol s with
          | Some v -> VarSet.add v vars
          | None -> vars)
    in
    BatEnum.fold
      (fun refs (var, _) -> VarSet.add var refs)
      (add_symbols (symbols (T.guard tr)) VarSet.empty)
      (T.transform tr)

  (* Interval abstract domain *)
  module Box = struct

    (* Variables not belonging to an interval store are implicitly mapped to
       top *)
    type store = Interval.t VarMap.t

    type t =
      | Store of store
      | Bottom

    type edge = int * tlabel * int

    let pp_store formatter store =
      let open Format in
      let pp_elt formatter (v, ivl) =
        fprintf formatter "@[%a -> %a@]" Var.pp v Interval.pp ivl
      in
      SrkUtil.pp_print_enum pp_elt formatter (VarMap.enum store)

    let _pp formatter prop =
      let open Format in
      match prop with
      | Bottom -> fprintf formatter "Bottom"
      | Store s when VarMap.is_empty s -> fprintf formatter "Top"
      | Store s -> pp_store formatter s

    let equal x y = match x, y with
      | Store x, Store y -> VarMap.equal Interval.equal x y
      | Bottom, Bottom -> true
      | _, _ -> false

    let bottom = Bottom
    let top = Store VarMap.empty

    let widening_store =
      VarMap.merge (fun _ x y -> match x, y with
            | Some x, Some y ->
              let result = Interval.widening x y in
              if Interval.equal result Interval.top then
                None
              else
                Some result
            | _, _ -> None)

    let widening x y =
      match x, y with
      | Bottom, x | x, Bottom -> x
      | Store x, Store y -> Store (widening_store x y)

    let join_store =
      VarMap.merge (fun _ x y -> match x, y with
          | Some x, Some y ->
            let result = Interval.join x y in
            if Interval.equal result Interval.top then
              None
            else
              Some result
          | _, _ -> None)

    let join x y =
      match x, y with
      | Bottom, x | x, Bottom -> x
      | Store x, Store y -> Store (join_store x y)

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

    let transform (_s, label, _t) prop =
      let context = Z3.mk_context [("timeout", "100")] in
      match prop, label with
      | Bottom, _ -> Bottom
      | Store store, Call (_, _) ->
        Store (VarMap.filter
                 (fun v _ -> not (Var.is_global v))
                 store)
      | Store store, Weight tr ->
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
        let vars = VarSet.elements (abstract_defs tr) in
        let objectives =
          List.map (fun v ->
              if T.mem_transform v tr then
                T.get_transform v tr
              else
                mk_const srk (Var.symbol_of v))
            vars
        in
        let result =
          match Nonlinear.optimize_box ~context srk guard objectives with
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
        result
  end

  module PredicateSet = struct
    include BatSet.Make(struct
        type t = C.t formula
        let compare = Formula.compare
      end)
    let pp formatter set =
      SrkUtil.pp_print_enum (Formula.pp srk) formatter (enum set)
  end

  module PAxBox = struct
    module PS = PredicateSet

    (* An abstract state consists of a set of predicates that hold and an
       interval store *)
    type t =
      | State of PS.t * Box.store
      | Bottom
    [@@deriving show]

    type edge = int * tlabel * int

    let join prop prop' =
      match prop, prop' with
      | Bottom, _ -> prop'
      | _, Bottom -> prop
      | State (predicates, store), State (predicates', store') ->
        State (PS.inter predicates predicates',
               Box.join_store store store')

    let normalize predicates store =
      let guard =
        mk_and srk ((Box.to_formula store)::(PS.elements predicates))
      in
      let context = Z3.mk_context [("timeout", "100")] in
      let variables =
        let add_vars predicate =
          Symbol.Set.fold (fun s vars ->
              match Var.of_symbol s with
              | Some v -> VarSet.add v vars
              | None -> vars)
            (symbols predicate)
        in
        VarSet.elements (PS.fold add_vars predicates VarSet.empty)
      in
      let objectives =
        List.map (fun v -> mk_const srk (Var.symbol_of v)) variables
      in
      match Nonlinear.optimize_box ~context srk guard objectives with
      | `Sat intervals ->
        List.fold_left2 (fun store v ivl ->
            VarMap.add v ivl store)
          store
          variables
          intervals
      | `Unknown -> store
      | `Unsat -> invalid_arg "normalize: abstract state is inconsistent"

    let widening prop prop' =
      match prop, prop' with
      | Bottom, _ -> prop'
      | _, Bottom -> prop
      | State (predicates, store), State (predicates', store') ->
        if PS.equal predicates predicates' then
          State (predicates, Box.widening_store store store')
        else if PS.subset predicates' predicates then
          let store = normalize predicates store in
          let store' = normalize predicates' store' in
          State (PS.inter predicates predicates', Box.join_store store store')
        else
          (* Possible if, e.g., some abstract post computation returns some
             Unknowns *)
          let predicates = PS.inter predicates predicates' in
          State (predicates, Box.widening_store store store')

    let equal prop prop' =
      match prop, prop' with
      | Bottom, Bottom -> true
      | State (predicates, store), State (predicates', store') ->
        PS.equal predicates predicates'
        && VarMap.equal Interval.equal store store'
      | _, _ -> false

    let top = State (PS.empty, VarMap.empty)
    let bottom = Bottom

    (* Universe is a map from variables to the set of all predicates that
       involve that variable *)
    let transform universe (s, label, t) prop =
      match label, prop with
      | (_, Bottom) -> bottom
      | (Call (_, _), State (predicates, store)) ->
        let store' =
          match Box.transform (s, label, t) (Box.Store store) with
          | Box.Store store' -> store'
          | Box.Bottom -> assert false
        in
        let predicates' =
          PS.filter (fun predicate ->
              Symbol.Set.for_all (fun sym ->
                  match Var.of_symbol sym with
                  | Some var -> not (Var.is_global var)
                  | None -> true)
                (symbols predicate))
            predicates
        in
        State (predicates', store')
      | (Weight tr, State (predicates, store)) ->
        logf ~level:`trace "In: %a" pp (State (predicates, store));
        logf ~level:`trace "Transition: %a" T.pp tr;

        let tr' =
          T.mul (T.assume (mk_and srk (PS.elements predicates))) tr
        in

        match Box.transform (s, Weight tr', t) (Box.Store store) with
        | Box.Bottom -> Bottom
        | Box.Store store' ->
          let context = Z3.mk_context [("timeout", "100")] in

          let predicates' =
            let solver = SrkZ3.Solver.make ~theory:"QF_LIRA" ~context srk in
            let postify =
              substitute_const srk (fun sym ->
                  match Var.of_symbol sym with
                  | Some var ->
                    if T.mem_transform var tr' then
                      T.get_transform var tr'
                    else
                      mk_const srk sym
                  | None -> mk_const srk sym)
            in
            (* Predicates that hold before the transition and which are not
               modified *)
            let unmodified_predicates =
              PS.filter (fun predicate ->
                  Symbol.Set.for_all (fun sym ->
                      match Var.of_symbol sym with
                      | Some var -> not (T.mem_transform var tr')
                      | None -> true)
                    (symbols predicate))
                predicates
            in
            (* Predicates that do not hold before the transition and may hold
               after *)
            let modified_predicates =
              let modified =
                VarSet.fold (fun v mu ->
                    PS.union mu (VarMap.find_default PS.empty v universe))
                  (abstract_defs tr)
                  PS.empty
              in
              PS.elements (PS.diff modified unmodified_predicates)
            in
            let indicators =
              List.map
                (fun _ -> mk_const srk (mk_symbol srk `TyBool))
                modified_predicates
            in
            SrkZ3.Solver.add solver [Nonlinear.uninterpret srk (T.guard tr')];

            List.iter2 (fun p i ->
                SrkZ3.Solver.add solver
                  [mk_if srk
                     i
                     (mk_not srk (Nonlinear.uninterpret srk (postify p)))])
              modified_predicates
              indicators;

            (* Assert relevant interval constraints *)
            uses tr' |> List.iter (fun v ->
                if VarMap.mem v store then
                  let ivl = VarMap.find v store in
                  let t = mk_const srk (Var.symbol_of v) in
                  begin match Interval.lower ivl with
                    | Some lo ->
                      SrkZ3.Solver.add solver [mk_leq srk (mk_real srk lo) t]
                    | None -> ()
                  end;
                  begin match Interval.upper ivl with
                    | Some hi ->
                      SrkZ3.Solver.add solver [mk_leq srk t (mk_real srk hi)]
                    | None -> ()
                  end);

            List.fold_left2 (fun set predicate indicator ->
                match SrkZ3.Solver.check ~assumptions:[indicator] solver  with
                | `Unsat -> PS.add predicate set
                | _ -> set)
              unmodified_predicates
              modified_predicates
              indicators
          in
          let res = State (predicates', store') in
          logf ~level:`trace "Out: %a" pp res;
          res
  end

  module IntervalAnalysis = Fixpoint.Make(WGG)(Box)
  module IntPair = struct
    type t = int * int [@@deriving ord]
    let equal (x,y) (x',y') = (x=x' && y=y')
    let hash = Hashtbl.hash
  end

  module IntPairPair = struct 
    type t = IntPair.t * IntPair.t [@@deriving ord]
    let equal (x, y) (x', y') = (x=x' && y=y')
    let hash = Hashtbl.hash 
  end 

  module PS = BatSet.Make(IntPair)
  module PPS = BatSet.Make(IntPairPair) (* used in inliner *)
  module PHT = BatHashtbl.Make(IntPair)
  module VHT = BatHashtbl.Make(Var)

  (* Remove temporary variables that are referenced by only one transition *)
  let remove_temporaries proj tg =
    (* Map each local variable to the set of transitions that refer to it *)
    let ref_map = VHT.create 991 in
    let add_ref var (u, v) =
      if not (proj var) then
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
            let tmp =
              List.fold_right VarSet.remove (uses tr) (PHT.find tmp_map (u, v))
            in
            Weight (T.exists (fun x -> not (VarSet.mem x tmp)) tr)
          with Not_found -> label)  

  let forward_invariants_ivl tg entry =
    let init v =
      if v = entry then Box.top
      else Box.bottom
    in
    let interval = IntervalAnalysis.analyze ~delay:3 tg init in
    let loop_references loop =
      let vertices = L.body loop in
      L.VertexSet.fold (fun u vars ->
          WG.fold_succ_e (fun (_, weight, v) vars ->
              match weight with
              | Weight tr when L.VertexSet.mem v vertices ->
                VarSet.union vars (references tr)
              | _ -> vars)
            tg
            u
            vars)
        vertices
        VarSet.empty
    in
    let invariants loop =
      let header = L.header loop in
      let invariant =
        match interval header with
        | Box.Bottom -> mk_false srk
        | Box.Store store ->
           VarSet.fold (fun v inv ->
               if VarMap.mem v store then
                 VarMap.add v (VarMap.find v store) inv
               else
                 inv)
             (loop_references loop)
             VarMap.empty
           |> Box.to_formula
      in
      logf "Found invariant at %d: %a"
        (L.header loop)
        (Formula.pp srk) invariant;
      (header, invariant)
    in
    List.map invariants (L.all_loops (L.loop_nest tg))

  let forward_invariants_ivl_pa predicates tg entry =
    let init v =
      if v = entry then PAxBox.top
      else PAxBox.bottom
    in
    let universe =
      List.fold_left (fun m predicate ->
          Symbol.Set.fold (fun sym m ->
              match Var.of_symbol sym with
              | Some var ->
                VarMap.modify_def
                  PredicateSet.empty
                  var
                  (PredicateSet.add predicate)
                  m
              | None -> m)
            (symbols predicate)
            m)
        VarMap.empty
        predicates
    in
    let module Analysis =
      Fixpoint.Make(WGG)(struct
          include PAxBox
          let transform = transform universe
        end)
    in
    let annotation = Analysis.analyze ~delay:3 tg init in
    let loop_references loop =
      let vertices = L.body loop in
      L.VertexSet.fold (fun u vars ->
          WG.fold_succ_e (fun (_, weight, v) vars ->
              match weight with
              | Weight tr when L.VertexSet.mem v vertices ->
                VarSet.union vars (references tr)
              | _ -> vars)
            tg
            u
            vars)
        vertices
        VarSet.empty
    in
    let invariants loop =
      let header = L.header loop in
        let invariant =
          match annotation header with
          | PAxBox.Bottom -> mk_false srk
          | PAxBox.State (predicates, store) ->
            let relevant = loop_references loop in
            let box_formula =
              VarSet.fold (fun v inv ->
                  if VarMap.mem v store then
                    VarMap.add v (VarMap.find v store) inv
                  else
                    inv)
                relevant
                VarMap.empty
              |> Box.to_formula
            in
            let relevant_predicates =
              PredicateSet.filter (fun predicate ->
                  Symbol.Set.exists (fun sym ->
                      match Var.of_symbol sym with
                      | Some var -> VarSet.mem var relevant
                      | None -> false)
                    (symbols predicate))
                predicates
            in
            mk_and srk (box_formula::(PredicateSet.elements relevant_predicates))
        in
        logf "Found invariant at %d: %a"
          header
          (Formula.pp srk) invariant;
        (header, invariant)
    in
    List.map invariants (L.all_loops (L.loop_nest tg))


  let inline ?(depth=(-1)) tg entry (displayer: t -> unit)= 
    let pmap = PHT.create 998 in (* y in pmap[x] means call from x->y *)
    let qmap = PHT.create 998 in (* (x, z) in qmap[y] means call from x->y via call-edge z *)
    let greatest = ref (WG.fold_vertex max tg (-1)) in
    PHT.add pmap (entry, -1) PS.empty;
    PHT.add qmap (entry, -1) PPS.empty;
    let procedures = 
      WG.fold_edges (fun (_, w, _) acc -> 
        match w with 
        | Call (x, y) -> 
          begin match PHT.find_opt pmap (x, y) with 
          | None -> 
            PHT.add pmap (x, y) PS.empty 
          | Some _ -> ()
          end;
          begin match PHT.find_opt qmap (x, y) with 
          | None -> 
            PHT.add qmap (x, y) PPS.empty 
          | Some _ -> () 
          end;
          PS.add (x, y) acc
        | _ -> acc 
        ) tg (PS.add (entry, -1) PS.empty) in 
    let rec dfs (proc: int * int) tg src (f: (vertex * vertex) -> vertex -> vertex * 'a label * vertex -> unit) (visited : ISet.t) = 
      Printf.printf "dfs: visiting %d\n" src;
      WG.fold_succ_e (fun (u, w, v) visited -> 
        f proc src (u, w, v);
        begin match ISet.find_opt v visited with 
            | None -> ISet.union (dfs proc tg v f (ISet.add v visited)) visited 
            | Some _ -> visited 
            end) tg src visited in 
      PS.iter (fun (x, y) -> 
        Printf.printf "populating p/qmaps with dfs... %d %d\n" x y;
        ignore @@ dfs (x, y) tg x (fun proc src (_, w, v) -> 
          match w with 
          | Call (x, y) -> 
            let caller_set = PHT.find pmap proc in 
            let callee_set = PHT.find qmap (x, y) in
            PHT.add pmap proc (PS.add (x, y) caller_set);
            PHT.add qmap (x, y) (PPS.add (proc, (src, v)) callee_set);
          | _ -> () 
          ) (ISet.add x ISet.empty)) procedures; (* populate pmap, qmap *)
      let compute_sinks () = 
        PS.fold (fun (x, y) acc -> (* compute sink locations to start inlining from *)
          match (PHT.find_opt pmap (x, y), PHT.find_opt qmap (x, y)) with 
          | Some callees, Some callers -> 
            (* a procedure is considered for inlining if it is (1) a sink in the call graph (2) at least one function calls it.*)
            if ((PS.cardinal callees) == 0) && ((PPS.cardinal callers) > 0) then PS.add (x, y) acc else 
              begin 
                Printf.printf "%d %d is not a sink; num callees = %d num callers = %d\n" x y (PS.cardinal callees) (PPS.cardinal callers);
                acc
              end 
          | (_, _) -> failwith ""
          ) procedures PS.empty in
      let copy_subgraph tg src = 
        let vertices = dfs (-1, -1) tg src (fun _ _ _ -> ()) (ISet.add src ISet.empty) in 
        let to_map = Hashtbl.create 998 in 
        let rtg = ref tg in 
          ISet.iter (fun x -> 
            greatest := !greatest + 1;
            Hashtbl.add to_map x (!greatest);
            rtg := WG.add_vertex !rtg !greatest
            ) vertices;
          ISet.iter (fun x -> 
              rtg := WG.fold_succ_e (fun (u, w, v) tg' -> 
                  WG.add_edge tg' (Hashtbl.find to_map u) w (Hashtbl.find to_map v)) 
                !rtg x !rtg) vertices;
          (!rtg, Hashtbl.find to_map)
      in let remove_subgraph tg src = 
        let vertices = dfs (-1, -1) tg src (fun _ _ _ -> ()) (ISet.add src ISet.empty) in 
        ISet.fold (fun vtx tg' -> WG.remove_vertex tg' vtx) vertices tg in 
      let inline_one tg (src, dst) (call_x, call_y) (call_src, call_dst) = 
        Printf.printf "inlining %d-%d into call edge %d-%d\n" src dst call_x call_y;
        let (tg, to_map) = copy_subgraph tg src in 
        let tg = WG.add_edge tg call_x (Weight T.one) (to_map src) in 
        let tg = WG.add_edge tg (to_map dst) (Weight T.one) call_y in 
        let tg = WG.remove_edge tg call_x call_y in
        let callees = PHT.find pmap (call_src, call_dst) in
        let callers = PHT.find qmap (src, dst) in 
        (* remove (src, dst) from callees list in caller *) 
        PHT.add pmap (call_src, call_dst) (PS.remove (src, dst) callees);
        (* remove (call_src, call_dst) from callers list *)
        PHT.add qmap (src, dst) (PPS.remove ((call_src, call_dst),(call_x, call_y)) callers);
        tg
      in let rec do_inline depth tg =
        if depth == 0 then tg else 
          let sinks = compute_sinks () in 
          let aux currproc tg = (* inline currproc into procedures that call it, assuming currproc is inlined. *)
            let inline_targets = PHT.find qmap currproc in 
              let tg' = 
                PPS.fold (fun (call_proc, (call_x, call_y)) tg -> 
                  Printf.printf "do_inline: at edge %d %d\n\n" call_x call_y;
                  inline_one tg currproc (call_x, call_y) call_proc
                ) inline_targets tg in 
                let (src, _) = currproc in 
                  remove_subgraph tg' src  
          in
            displayer tg;
            match PS.cardinal sinks with 
              | n when n > 0 ->  
                Printf.printf "inliner: there are %d sinks to inline \n" n;
                let tg' = (PS.fold aux sinks tg) in
                   tg'
                |> do_inline (
                  Printf.printf "doing more inling...\n";
                  if depth > 0 then depth - 1 else depth)
              | _ -> Printf.printf "no more sinks to inline. done\n"; tg 
        in let result = do_inline depth tg in Printf.printf "inlining done"; result 


  

  let simplify ?(try_rtc=true) p tg =
    let rec go tg =
      Printf.printf "simplify: simplifying...\n";
      let continue = ref false in
      let tg' =
        WG.fold_vertex (fun v tg ->
            let ug = WG.forget_weights tg in
            if (p v
                || WG.mem_edge tg v v
                || (WG.U.in_degree ug v != 1
                    && WG.U.out_degree ug v != 1))
            then
              begin if try_rtc then begin 
                  begin if WG.mem_edge tg v v then
                      match WG.edge_weight tg v v with
                      | Weight tr ->
                        (try begin match T.try_rtc tr with
                        | Some rtc ->
                          let u = -1 in
                          (try
                              let tg = WG.remove_edge tg v v in
                              let tg =
                                WG.contract_vertex (WG.split_vertex tg v (Weight rtc) u) u
                              in
                              continue := true;
                              tg
                            with _ -> tg)
                        | None -> tg end
                          with _ -> tg)
                      | Call (_, _) -> tg
                    else
                      tg
                    end
                  end 
                else tg 
              end
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

  let loop_headers_live tg =
    let loop_references loop =
      let vertices = L.body loop in
      L.VertexSet.fold (fun u vars ->
          WG.fold_succ_e (fun (_, weight, v) vars ->
              match weight with
              | Weight tr when L.VertexSet.mem v vertices ->
                VarSet.union vars (references tr)
              | _ -> vars)
            tg
            u
            vars)
        vertices
        VarSet.empty
    in
    let rec live hl lnf =
      match lnf with
      | `Vertex _ -> hl
      | `Loop loop ->
         let references = loop_references loop in
         let header = L.header loop in
         List.fold_left live ((header, references)::hl) (L.children loop)
    in
    List.fold_left live [] (L.loop_nest tg)

  type 'a abstract_domain =
    { abstract : C.t Abstract.Solver.t -> symbol list -> 'a -> 'a
    ; bottom : 'a
    ; top : 'a
    ; join : 'a -> 'a -> 'a
    ; formula_of : 'a -> C.t formula
    ; exists : (symbol -> bool) -> 'a -> 'a
    ; equal : 'a -> 'a -> bool }

  let product dA dB =
    let abstract solver symbols (a, b) =
      let a' = dA.abstract solver symbols a in
      let b' = dB.abstract solver symbols b in
      (a', b')
    in
    let bottom = (dA.bottom, dB.bottom) in
    let top = (dA.top, dB.top) in
    let formula_of (a, b) =
      mk_and srk [dA.formula_of a; dB.formula_of b]
    in
    let exists p (a, b) = (dA.exists p a, dB.exists p b) in
    let equal (a1, b1) (a2, b2) =
      dA.equal a1 a2 && dB.equal b1 b2
    in
    let join (a1, b1) (a2, b2) =
      (dA.join a1 a2, dB.join b1 b2)
    in
    { abstract; bottom; top; formula_of; exists; equal; join }

  let predicate_abs universe =
    let abstract solver _ universe =
      Abstract.PredicateAbs.abstract solver universe
    in
    let top = Expr.Set.empty in
    let bottom = Expr.Set.of_list universe in
    let formula_of = Abstract.PredicateAbs.formula_of srk in
    let exists = Abstract.PredicateAbs.exists in
    let equal = Expr.Set.equal in
    let join = Abstract.PredicateAbs.join in
    { abstract; bottom; top; formula_of; exists; equal; join }

  let affine_relation =
    let zero = mk_zero srk in
    let trivial = Linear.QQVector.of_term QQ.one Linear.const_dim in
    let formula_of relations =
      List.map (fun vec -> mk_eq srk (Linear.of_linterm srk vec) zero) relations
      |> mk_and srk
    in
    let project keep relations =
      let keep_space =
        Int.Set.fold (fun dim space ->
            (Linear.QQVector.of_term QQ.one dim)::space)
          keep
          []
      in
      Linear.QQVectorSpace.intersect keep_space relations
    in
    let abstract solver symbols relations =
      Abstract.LinearSpan.affine_hull solver ~bottom:relations symbols
    in
    let module IntSet = SrkUtil.Int.Set in
    let exists p relations =
      let keep =
        List.fold_left (fun dimensions vec ->
            BatEnum.fold (fun dimensions (_, dim) ->
                if p (symbol_of_int dim) then
                  IntSet.add dim dimensions
                else
                  dimensions)
              dimensions
              (Linear.QQVector.enum vec))
          (IntSet.singleton Linear.const_dim)
          relations
      in
      project keep relations
    in
    let bottom = [trivial] in
    let equal = Linear.QQVectorSpace.equal in
    let join = Linear.QQVectorSpace.intersect in
    let top = [] in
    { abstract; top; bottom; formula_of; exists; equal; join }

  let sign =
    let abstract solver symbols bottom =
      let terms = List.map (mk_const srk) symbols in
      Abstract.Sign.abstract solver ~bottom terms
    in
    let top = Abstract.Sign.top in
    let bottom = Abstract.Sign.bottom in
    let formula_of = Abstract.Sign.formula_of srk in
    let exists = Abstract.Sign.exists in
    let equal = Abstract.Sign.equal in
    let join = Abstract.Sign.join in
    { abstract; top; bottom; formula_of; exists; equal; join }

  let forward_invariants domain tg entry =
    let update ~pre weight ~post =
      match weight with
      | Weight tr ->
        (* Replace modified variable symbols with fresh Skolem
           constants.  This allows the post-condition of the
           transition formula tf to be expressed over the symbols
           associated with the variables via Var.of_symbol /
           Var.symbol_of *)
        let subst =
          BatEnum.fold (fun subst (v, _) ->
              let pre_sym = mk_symbol srk ((Var.typ v) :> typ) in
              let post_sym = Var.symbol_of v in
              Symbol.Map.add post_sym (mk_const srk pre_sym) subst)
            Symbol.Map.empty
            (T.transform tr)
        in
        let transform_eqs =
          T.transform tr
          /@ (fun (v, t) ->
              mk_eq srk (mk_const srk (Var.symbol_of v)) (substitute_map srk subst t))
          |> BatList.of_enum
        in
        let pre_formula = domain.formula_of pre in
        let tf =
          mk_and srk (substitute_map srk subst (T.guard tr)
                      ::substitute_map srk subst pre_formula
                      ::transform_eqs)
          |> Nonlinear.uninterpret srk
        in
        let symbols = (* Symbols in pre or defined by tr *)
          VarSet.fold
            (fun v set ->
               Symbol.Set.add (Var.symbol_of v) set)
            (references tr)
            (Symbol.Set.filter
               (fun s -> Var.of_symbol s != None)
               (symbols pre_formula))
          |> Symbol.Set.elements
        in
        let solver = Abstract.Solver.make ~theory:`LIRA srk tf in
        let post' = domain.abstract solver symbols post in
        if domain.equal post' post then
          None
        else
          Some post'

      | Call (_, _) ->
        let is_local s =
          match Var.of_symbol s with
          | None -> true
          | Some v -> not (Var.is_global v)
        in
        let post' = domain.exists is_local pre in
        if domain.equal post' post then
          None
        else
          Some (domain.join post post')
    in
    let init v =
      if v = entry then
        domain.top
      else
        domain.bottom
    in
    WG.forward_analysis tg ~entry ~update ~init
end
