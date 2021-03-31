open BatPervasives
open Syntax

include Log.Make(struct let name = "srk.transitionSystem" end)

module WG = WeightedGraph
module Int = SrkUtil.Int

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
       val transform : t -> (var * C.t term) BatEnum.t
       val mem_transform : var -> t -> bool
       val get_transform : var -> t -> C.t term
       val assume : C.t formula -> t
       val mul : t -> t -> t
       val add : t -> t -> t
       val zero : t
       val one : t
       val star : t -> t
       val exists : (var -> bool) -> t -> t
     end)
= struct

  type vertex = int
  type transition = T.t
  type tlabel = T.t label

  type query = T.t WG.RecGraph.weight_query

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
            let solver = SrkZ3.mk_solver ~theory:"QF_LIRA" ~context srk in
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
                match SrkZ3.Solver.check solver [indicator] with
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

  let simplify p tg =
    let rec go tg =
      let continue = ref false in
      let tg' =
        WG.fold_vertex (fun v tg ->
            let ug = WG.forget_weights tg in
            if (p v
                || WG.mem_edge tg v v
                || WG.U.in_degree ug v != 1
                || WG.U.out_degree ug v != 1)
            then
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

  module type AbstractDomain = Abstract.MakeAbstractRSY(C).Domain

  module type IncrAbstractDomain = sig
    include AbstractDomain
    val incr_abstract : C.t Interpretation.interpretation list -> symbol list -> C.t Smt.Solver.t -> t -> (t * C.t Interpretation.interpretation list)
  end

  module LiftIncr (A : AbstractDomain) = struct
    include A
    let incr_abstract models symbols solver post =
      let start =      
        List.fold_left (fun a m -> join a (of_model m symbols)) post models
      in
      let rec fix prop models =
        Smt.Solver.add solver [mk_not srk (formula_of prop)];
        match Smt.Solver.get_model solver with
        | `Sat m ->
          fix (join (of_model m symbols) prop) (m::models)
        | `Unsat -> (prop, models)
        | `Unknown ->
          logf ~level:`warn "Unknown result in affine invariant update";
          (top, models)
      in
      Smt.Solver.push solver;
      let result = fix start models in
      Smt.Solver.pop solver 1;
      result
  end

  module ProductIncr (A : IncrAbstractDomain)(B : IncrAbstractDomain) = struct
    type t = A.t * B.t
    let top = (A.top, B.top)
    let bottom = (A.bottom, B.bottom)
    let exists p (v1, v2) = (A.exists p v1, B.exists p v2)
    let join (v1, v2) (v1', v2') = (A.join v1 v1', B.join v2 v2')
    let equal (v1, v2) (v1', v2') = A.equal v1 v1' && B.equal v2 v2'
    let of_model  m symbols = (A.of_model m symbols, B.of_model m symbols)
    let formula_of  (v1, v2) = mk_and C.context [A.formula_of v1; B.formula_of v2]

    let incr_abstract models symbols solver (post_a, post_b) =
      let (a, models) = A.incr_abstract models symbols solver post_a in
      let (b, models) = B.incr_abstract models symbols solver post_b in
      ((a,b), models)
  end

  let forward_invariants (type a) (module D : IncrAbstractDomain with type t = a) tg entry =
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
        let pre_formula = D.formula_of pre in
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
        let solver = Smt.mk_solver srk in
        Smt.Solver.add solver [tf];
        let (post', _) = D.incr_abstract [] symbols solver post in
        if D.equal post' post then
          None
        else
          Some post'

      | Call (_, _) ->
        let is_local s =
          match Var.of_symbol s with
          | None -> true
          | Some v -> not (Var.is_global v)
        in
        let post' = D.exists is_local pre in
        if D.equal post' post then
          None
        else
          Some (D.join post post')
    in
    let init v =
      if v = entry then
        D.top
      else
        D.bottom
    in
    WG.forward_analysis tg ~entry ~update ~init
end
