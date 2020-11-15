open Syntax
open BatPervasives

include Log.Make(struct let name = "srk.iteration" end)

module V = Linear.QQVector
module CS = CoordinateSystem
module TF = TransitionFormula
module WG = WeightedGraph

module type PreDomain = sig
  type 'a t
  val pp : 'a context -> (symbol * symbol) list -> Format.formatter -> 'a t -> unit
  val exp : 'a context -> (symbol * symbol) list -> 'a term -> 'a t -> 'a formula
  val abstract : 'a context -> 'a TransitionFormula.t -> 'a t
end

module type PreDomainIter = sig
  include PreDomain
  val equal : ('a context) -> (symbol * symbol) list -> 'a t -> 'a t -> bool
  val join : ('a context) -> (symbol * symbol) list -> 'a t -> 'a t -> 'a t
  val widen : ('a context) -> (symbol * symbol) list -> 'a t -> 'a t -> 'a t
end

module type PreDomainWedge = sig
  include PreDomain
  val abstract_wedge : 'a context -> (symbol * symbol) list -> 'a Wedge.t -> 'a t
end

module type PreDomainWedgeIter = sig
  include PreDomainIter
  val abstract_wedge : 'a context -> (symbol * symbol) list -> 'a Wedge.t -> 'a t
end

module type Domain = sig
  type 'a t
  val pp : Format.formatter -> 'a t -> unit
  val closure : 'a t -> 'a formula
  val abstract : 'a context -> 'a TransitionFormula.t -> 'a t
  val tr_symbols : 'a t -> (symbol * symbol) list
end

module WedgeGuard = struct
  type 'a t =
    { precondition : 'a Wedge.t;
      postcondition : 'a Wedge.t }

  let pp _ _ formatter iter =
    Format.fprintf formatter "pre:@;  @[<v 0>%a@]@;post:@;  @[<v 0>%a@]"
      Wedge.pp iter.precondition
      Wedge.pp iter.postcondition

  let abstract_wedge _ tr_symbols wedge =
    let pre_symbols = TF.pre_symbols tr_symbols in
    let post_symbols = TF.post_symbols tr_symbols in
    let precondition =
      Wedge.exists (not % flip Symbol.Set.mem post_symbols) wedge
    in
    let postcondition =
      Wedge.exists (not % flip Symbol.Set.mem pre_symbols) wedge
    in
    { precondition; postcondition }

  let abstract srk tf =
    let wedge = TF.wedge_hull srk tf in
    abstract_wedge srk (TF.symbols tf) wedge

  let exp srk tr_symbols loop_counter guard =
    mk_or srk [mk_and srk [mk_eq srk loop_counter (mk_real srk QQ.zero);
                           TF.formula (TF.identity srk tr_symbols)];
               mk_and srk [mk_leq srk (mk_real srk QQ.one) loop_counter;
                           Wedge.to_formula guard.precondition;
                           Wedge.to_formula guard.postcondition]]

  let equal _ _ iter iter' =
    Wedge.equal iter.precondition iter'.precondition
    && Wedge.equal iter.postcondition iter'.postcondition

  let join _ _ iter iter' =
    { precondition = Wedge.join iter.precondition iter'.precondition;
      postcondition = Wedge.join iter.postcondition iter'.postcondition }

  let widen _ _ iter iter' =
    { precondition = Wedge.widen iter.precondition iter'.precondition;
      postcondition = Wedge.widen iter.postcondition iter'.postcondition }
end

module PolyhedronGuard = struct
  type 'a polyhedron = ('a, Polka.strict Polka.t) SrkApron.property
  type 'a t =
    { precondition : 'a polyhedron;
      postcondition : 'a polyhedron }

  let pp _ _ formatter iter =
    Format.fprintf formatter "pre:@;  @[<v 0>%a@]@;post:@;  @[<v 0>%a@]"
      SrkApron.pp iter.precondition
      SrkApron.pp iter.postcondition

  let abstract srk tf =
    let phi = Nonlinear.linearize srk (TF.formula tf) in
    let phi =
      rewrite srk ~down:(nnf_rewriter srk) phi
    in
    let post_symbols = TF.post_symbols (TF.symbols tf) in
    let pre_symbols = TF.pre_symbols (TF.symbols tf) in
    let man = Polka.manager_alloc_strict () in
    let precondition =
      let exists x =
        TF.exists tf x && not (Symbol.Set.mem x post_symbols)
      in
      Abstract.abstract ~exists srk man phi
    in
    let postcondition =
      let exists x =
        TF.exists tf x && not (Symbol.Set.mem x pre_symbols)
      in
      Abstract.abstract ~exists srk man phi
    in
    { precondition; postcondition }

  let exp srk tr_symbols loop_counter guard =
    mk_or srk [mk_and srk [mk_eq srk loop_counter (mk_real srk QQ.zero);
                           TF.formula (TF.identity srk tr_symbols)];
               mk_and srk [mk_leq srk (mk_real srk QQ.one) loop_counter;
                           SrkApron.formula_of_property guard.precondition;
                           SrkApron.formula_of_property guard.postcondition]]

  let equal _ _ iter iter' =
    SrkApron.equal iter.precondition iter'.precondition
    && SrkApron.equal iter.postcondition iter'.postcondition

  let join _ _ iter iter' =
    { precondition = SrkApron.join iter.precondition iter'.precondition;
      postcondition = SrkApron.join iter.postcondition iter'.postcondition }

  let widen _ _ iter iter' =
    { precondition = SrkApron.widen iter.precondition iter'.precondition;
      postcondition = SrkApron.widen iter.postcondition iter'.postcondition }

  let precondition guard = guard.precondition
  let postcondition guard = guard.postcondition
end

module LinearGuard = struct
  type 'a t =
    { precondition : 'a formula;
      postcondition : 'a formula }

  let abstract_presburger_rewriter srk expr =
    match Expr.refine srk expr with
    | `Formula phi -> begin match Formula.destruct srk phi with
        | `Atom (_, _, _) ->
          if Quantifier.is_presburger_atom srk phi then
            expr
          else
            (mk_true srk :> ('a,typ_fo) expr)
        | _ -> expr
      end
    | _ -> expr

  let pp srk _ formatter guard =
    Format.fprintf formatter
      "@[<v 0>precondition: @[<hov> %a@]@;postcondition: @[<hov> %a@]@]"
      (Formula.pp srk) guard.precondition
      (Formula.pp srk) guard.postcondition

  let abstract srk tf =
    let phi =
      (TF.formula tf)
      |> rewrite srk ~up:(abstract_presburger_rewriter srk)
      |> rewrite srk ~down:(nnf_rewriter srk)
    in
    let tr_symbols = TF.symbols tf in
    let exists = TF.exists tf in
    let pre_symbols = TF.pre_symbols tr_symbols in
    let post_symbols = TF.post_symbols tr_symbols in
    let lin_phi = Nonlinear.linearize srk phi in
    let precondition =
      Quantifier.mbp
        srk
        (fun x -> exists x && not (Symbol.Set.mem x post_symbols))
        lin_phi
    in
    let postcondition =
      Quantifier.mbp
        srk
        (fun x -> exists x && not (Symbol.Set.mem x pre_symbols))
        lin_phi
    in
    { precondition; postcondition }

  let exp srk tr_symbols loop_counter guard =
    mk_or srk [mk_and srk [mk_eq srk loop_counter (mk_real srk QQ.zero);
                           TF.formula (TF.identity srk tr_symbols)];
               mk_and srk [mk_leq srk (mk_real srk QQ.one) loop_counter;
                           guard.precondition;
                           guard.postcondition]]

  let join srk _ guard guard' =
    { precondition = mk_or srk [guard.precondition; guard'.precondition];
      postcondition = mk_or srk [guard.postcondition; guard'.postcondition] }

  let widen srk _ guard guard' =
    let man = Polka.manager_alloc_strict () in
    let widen_formula phi psi =
      if Smt.equiv srk phi psi = `Yes then phi
      else
        let p = Abstract.abstract srk man phi in
        let p' = Abstract.abstract srk man psi in
        SrkApron.formula_of_property (SrkApron.widen p p')
    in
    { precondition = widen_formula guard.precondition guard'.precondition;
      postcondition = widen_formula guard.postcondition guard'.postcondition }

  let equal srk _ guard guard' =
    Smt.equiv srk guard.precondition guard'.precondition = `Yes
    && Smt.equiv srk guard.postcondition guard'.postcondition = `Yes
end

module LinearRecurrenceInequation = struct
  type 'a t = ('a term * [ `Geq | `Eq ] * QQ.t) list

  let pp srk _ formatter lr =
    Format.fprintf formatter "@[<v 0>";
    lr |> List.iter (fun (t, op, k) ->
        let opstring = match op with
          | `Geq -> ">="
          | `Eq -> "="
        in
        Format.fprintf formatter "%a %s %a@;" (Term.pp srk) t opstring QQ.pp k);
    Format.fprintf formatter "@]"

  let abstract srk tf =
    let phi =
      TF.formula tf
      |> rewrite srk ~down:(nnf_rewriter srk)
      |> Nonlinear.linearize srk
    in
    let delta =
      List.map (fun (s,_) ->
          let name = "delta_" ^ (show_symbol srk s) in
          mk_symbol srk ~name (typ_symbol srk s))
        (TF.symbols tf)
    in
    let delta_map =
      List.fold_left2 (fun map delta (s,s') ->
          Symbol.Map.add
            delta
            (mk_sub srk (mk_const srk s') (mk_const srk s))
            map)
        Symbol.Map.empty
        delta
        (TF.symbols tf)
    in
    let delta_polyhedron =
      let man = Polka.manager_alloc_strict () in
      let exists x = Symbol.Map.mem x delta_map in
      let delta_constraints =
        Symbol.Map.fold (fun s diff xs ->
            (mk_eq srk (mk_const srk s) diff)::xs)
          delta_map
          []
      in
      Abstract.abstract ~exists srk man (mk_and srk (phi::delta_constraints))
      |> SrkApron.formula_of_property
    in
    let constraint_of_atom atom =
      match Formula.destruct srk atom with
      | `Atom (op, s, t) ->
        let t = V.sub (Linear.linterm_of srk t) (Linear.linterm_of srk s) in
        let (k, t) = V.pivot Linear.const_dim t in
        let term = substitute_map srk delta_map (Linear.of_linterm srk t) in
        begin match op with
          | `Leq | `Lt -> (term, `Geq, QQ.negate k)
          | `Eq -> (term, `Eq, QQ.negate k)
        end
      | _ -> assert false
    in
    match Formula.destruct srk delta_polyhedron with
      | `And xs -> List.map constraint_of_atom xs
      | `Tru -> []
      | `Fls -> [mk_real srk QQ.zero, `Eq, QQ.one]
      | _ -> [constraint_of_atom delta_polyhedron]

  let exp srk _ loop_counter lr =
    List.map (fun (delta, op, c) ->
        match op with
        | `Eq ->
          mk_eq srk (mk_mul srk [mk_real srk c; loop_counter]) delta
        | `Geq ->
          mk_leq srk (mk_mul srk [mk_real srk c; loop_counter]) delta)
      lr
    |> mk_and srk
end

module NonlinearRecurrenceInequation = struct
  type 'a t = ('a term * [ `Geq | `Eq ] * 'a term) list

  let pp srk _ formatter lr =
    Format.fprintf formatter "NLE: @[<v 0>";
    lr |> List.iter (fun (t, op, k) ->
        let opstring = match op with
          | `Geq -> ">="
          | `Eq -> "="
        in
        Format.fprintf formatter "%a %s %a@;" (Term.pp srk) t opstring (Term.pp srk) k);
    Format.fprintf formatter "@]"

  module QQXs = Polynomial.QQXs

  let abstract_delta_wedge srk delta_wedge delta delta_map =
    let cs = Wedge.coordinate_system delta_wedge in
    let delta_dim =
      let dims =
        List.fold_left (fun dims delta ->
            try SrkUtil.Int.Set.add (CS.cs_term_id cs (`App (delta, []))) dims
            with Not_found -> dims)
          SrkUtil.Int.Set.empty
          delta
      in
      fun i -> SrkUtil.Int.Set.mem i dims
    in
    let constraint_of_atom atom =
      match Formula.destruct srk atom with
      | `Atom (op, s, t) ->
        let t = V.sub (CS.vec_of_term cs t) (CS.vec_of_term cs s) in
        let (lhs, rhs) =
          BatEnum.fold (fun (lhs, rhs) (coeff, dim) ->
              if delta_dim dim then
                (V.add_term coeff dim lhs, rhs)
              else
                (lhs, V.add_term (QQ.negate coeff) dim rhs))
            (V.zero, V.zero)
            (V.enum t)
        in
        if V.equal lhs V.zero then
          None
        else
          let lhs = substitute_map srk delta_map (CS.term_of_vec cs lhs) in
          let rhs = CS.term_of_vec cs rhs in
          begin match op with
            | `Leq | `Lt -> Some (lhs, `Geq, rhs)
            | `Eq -> Some (lhs, `Eq, rhs)
          end
      | _ -> assert false
    in
    if Wedge.is_bottom delta_wedge then
      []
    else
      BatList.filter_map constraint_of_atom (Wedge.to_atoms delta_wedge)

  let make_deltas srk tr_symbols =
    let delta =
      List.map (fun (s,_) ->
          let name = "delta_" ^ (show_symbol srk s) in
          mk_symbol srk ~name (typ_symbol srk s))
        tr_symbols
    in
    let delta_map =
      List.fold_left2 (fun map delta (s,s') ->
          Symbol.Map.add
            delta
            (mk_sub srk (mk_const srk s') (mk_const srk s))
            map)
        Symbol.Map.empty
        delta
        tr_symbols
    in
    (delta, delta_map)

  let abstract_wedge srk tr_symbols wedge =
    let (delta,delta_map) = make_deltas srk tr_symbols in
    let syms =
      List.fold_left (fun set (s,s') ->
          Symbol.Set.add s (Symbol.Set.add s' set))
        Symbol.Set.empty
        tr_symbols
    in
    let delta_wedge =
      let exists x = not (Symbol.Set.mem x syms) in
      let subterm x = not (Symbol.Map.mem x delta_map) in
      let delta_constraints =
        Symbol.Map.fold (fun s diff xs ->
            (mk_eq srk (mk_const srk s) diff)::xs)
          delta_map
          []
      in
      let delta_wedge = Wedge.copy wedge in
      Wedge.meet_atoms delta_wedge delta_constraints;
      Wedge.exists ~subterm exists delta_wedge
    in
    abstract_delta_wedge srk delta_wedge delta delta_map

  let abstract srk tf =
    let (delta,delta_map) = make_deltas srk (TF.symbols tf) in
    let syms =
      List.fold_left (fun set (s,s') ->
          Symbol.Set.add s (Symbol.Set.add s' set))
        Symbol.Set.empty
        (TF.symbols tf)
    in
    let delta_wedge =
      let exists x =
        Symbol.Map.mem x delta_map || (TF.exists tf x && not (Symbol.Set.mem x syms))
      in
      let subterm x = not (Symbol.Map.mem x delta_map) in
      let delta_constraints =
        Symbol.Map.fold (fun s diff xs ->
            (mk_eq srk (mk_const srk s) diff)::xs)
          delta_map
          []
      in
      mk_and srk ((TF.formula tf)::delta_constraints)
      |> Wedge.abstract ~subterm ~exists srk
    in
    abstract_delta_wedge srk delta_wedge delta delta_map

  let exp srk _ loop_counter lr =
    List.map (fun (delta, op, c) ->
        match op with
        | `Eq ->
          mk_eq srk (mk_mul srk [c; loop_counter]) delta
        | `Geq ->
          mk_leq srk (mk_mul srk [c; loop_counter]) delta)
      lr
    |> mk_and srk
end

module Product (A : PreDomain) (B : PreDomain) = struct
  type 'a t = 'a A.t * 'a B.t

  let pp srk tr_symbols formatter (a, b) =
    Format.fprintf formatter "%a@;%a"
      (A.pp srk tr_symbols) a
      (B.pp srk tr_symbols) b

  let exp srk tr_symbols loop_counter (a, b) =
    mk_and srk [A.exp srk tr_symbols loop_counter a;
                B.exp srk tr_symbols loop_counter b]

  let abstract srk tf =
    (A.abstract srk tf, B.abstract srk tf)
end

module Split (Iter : PreDomain) = struct
  type 'a t = ('a, typ_bool, 'a Iter.t * 'a Iter.t) Expr.Map.t

  let pp srk tr_symbols formatter split_iter =
    let pp_elt formatter (pred,(left,right)) =
      Format.fprintf formatter "[@[<v 0>%a@; %a@; %a@]]"
        (Formula.pp srk) pred
        (Iter.pp srk tr_symbols) left
        (Iter.pp srk tr_symbols) right
    in
    Format.fprintf formatter "<@[<v 0>Split @[<v 0>%a@]@]>"
      (SrkUtil.pp_print_enum_nobox pp_elt) (Expr.Map.enum split_iter)


  let base_bottom srk tr_symbols =
    Iter.abstract srk (TF.make (mk_false srk) tr_symbols)

  let abstract srk tf =
    let body = TF.formula tf in
    let tr_symbols = TF.symbols tf in
    let exists = TF.exists tf in
    let post_symbols = TF.post_symbols tr_symbols in
    let predicates =
      let preds = ref Expr.Set.empty in
      let prestate sym = exists sym && not (Symbol.Set.mem sym post_symbols) in
      let rr expr =
        match destruct srk expr with
        | `Not phi ->
          if Symbol.Set.for_all prestate (symbols phi) then
            preds := Expr.Set.add phi (!preds);
          expr
        | `Atom (op, s, t) ->
          let phi =
            match op with
            | `Eq -> mk_eq srk s t
            | `Leq -> mk_leq srk s t
            | `Lt -> mk_lt srk s t
          in
          begin
          if Symbol.Set.for_all prestate (symbols phi) then
            let redundant = match op with
              | `Eq -> false
              | `Leq -> Expr.Set.mem (SrkSimplify.simplify_terms srk (mk_lt srk t s)) (!preds)
              | `Lt -> Expr.Set.mem (SrkSimplify.simplify_terms srk (mk_leq srk t s)) (!preds)
            in
            if not redundant then
              preds := Expr.Set.add phi (!preds)
          end;
          expr
        | _ -> expr
      in
      ignore (rewrite srk ~up:rr body);
      BatList.of_enum (Expr.Set.enum (!preds))
    in
    let uninterp_body =
      rewrite srk
        ~up:(Nonlinear.uninterpret_rewriter srk)
        body
    in
    let solver = Smt.mk_solver srk in
    Smt.Solver.add solver [uninterp_body];
    let sat_modulo_body psi =
      let psi =
        rewrite srk
          ~up:(Nonlinear.uninterpret_rewriter srk)
          psi
      in
      Smt.Solver.push solver;
      Smt.Solver.add solver [psi];
      let result = Smt.Solver.check solver [] in
      Smt.Solver.pop solver 1;
      result
    in
    let is_split_predicate psi =
      (sat_modulo_body psi = `Sat)
      && (sat_modulo_body (mk_not srk psi) = `Sat)
    in
    let post_map = TF.post_map srk tr_symbols in
    let postify =
      let subst sym =
        if Symbol.Map.mem sym post_map then
          Symbol.Map.find sym post_map
        else
          mk_const srk sym
      in
      substitute_const srk subst
    in
    let abstract formula =
      Iter.abstract srk (TF.make ~exists formula tr_symbols)
    in
    let add_split_predicate split_iter psi =
      if is_split_predicate psi then
        let not_psi = mk_not srk psi in
        let post_psi = postify psi in
        let post_not_psi = postify not_psi in
        let psi_body = mk_and srk [body; psi] in
        let not_psi_body = mk_and srk [body; not_psi] in
        if sat_modulo_body (mk_and srk [psi; post_not_psi]) = `Unsat then
          (* {psi} body {psi} -> body* = ([not psi]body)*([psi]body)* *)
          let left_abstract = abstract not_psi_body in
          let right_abstract = abstract psi_body in
          Expr.Map.add not_psi (left_abstract, right_abstract) split_iter
        else if sat_modulo_body (mk_and srk [not_psi; post_psi]) = `Unsat then
          (* {not phi} body {not phi} -> body* = ([phi]body)*([not phi]body)* *)
          let left_abstract = abstract psi_body in
          let right_abstract = abstract not_psi_body in
          Expr.Map.add psi (left_abstract, right_abstract) split_iter
        else
          split_iter
      else
        split_iter
    in
    let split_iter =
      List.fold_left add_split_predicate Expr.Map.empty predicates
    in
    (* If there are no predicates that can split the loop, split on true *)
    let split_iter =
      if Expr.Map.is_empty split_iter then
        Expr.Map.add
          (mk_true srk)
          (Iter.abstract srk tf, base_bottom srk tr_symbols)
          Expr.Map.empty
      else
        split_iter
    in
    split_iter

  let exp srk tr_symbols loop_counter split_iter =
    Expr.Map.enum split_iter
    /@ (fun (predicate, (left, right)) ->
        let not_predicate = mk_not srk predicate in
        let left_counter = mk_const srk (mk_symbol srk ~name:"K" `TyInt) in
        let right_counter = mk_const srk (mk_symbol srk ~name:"K" `TyInt) in
        let left_closure =
          mk_and srk [Iter.exp srk tr_symbols left_counter left;
                      mk_or srk [mk_eq srk (mk_real srk QQ.zero) left_counter;
                                 predicate]]
        in
        let right_closure =
          mk_and srk [Iter.exp srk tr_symbols right_counter right;
                      mk_or srk [mk_eq srk (mk_real srk QQ.zero) right_counter;
                                 not_predicate]]
        in
        let left_right =
          TF.mul srk
            (TF.make left_closure tr_symbols)
            (TF.make right_closure tr_symbols)
          |> TF.formula
        in
        mk_and srk [left_right;
                    mk_eq srk (mk_add srk [left_counter; right_counter]) loop_counter])
    |> BatList.of_enum
    |> mk_and srk
end

module MakeDomain (Iter : PreDomain) = struct
  type 'a t =
    { srk : 'a context;
      tr_symbols : (symbol * symbol) list;
      iter : 'a Iter.t }

  let pp formatter iter =
    Format.fprintf formatter "{@[<v 1>%a@]}"
      (Iter.pp iter.srk iter.tr_symbols) iter.iter

  let closure iter =
    let srk = iter.srk in
    let loop_counter_sym = mk_symbol srk ~name:"K" `TyInt in
    let loop_counter = mk_const srk loop_counter_sym in
    mk_and srk [Iter.exp iter.srk iter.tr_symbols loop_counter iter.iter;
                mk_leq srk (mk_real srk QQ.zero) loop_counter]

  let abstract srk tf =
    let iter = Iter.abstract srk tf in
    let tr_symbols = TF.symbols tf in
    { srk; tr_symbols; iter }

  let tr_symbols iter = iter.tr_symbols
end

module ProductWedge (A : PreDomainWedge) (B : PreDomainWedge) = struct
  include Product(A)(B)

  let abstract_wedge srk tr_symbols wedge =
    (A.abstract_wedge srk tr_symbols wedge,
     B.abstract_wedge srk tr_symbols wedge)

  let abstract srk tf =
    abstract_wedge srk (TF.symbols tf) (TF.wedge_hull srk tf)
end


(* A transition p(x,x') predicate is invariant for a transition relation T(x,x') if
   T(x,x') /\ T(x',x'') /\ p(x,x') |= p(x',x'')
   (i.e., if p holds on some iteration, it must hold on all subsequent iterations).
   This procedure finds the subset of the input set of predicates that are invariant *)
let invariant_transition_predicates srk tf predicates =
  (* map' sends primed vars to midpoints; map sends unprimed vars to midpoints *)
  let (map', map) =
    List.fold_left (fun (subst1, subst2) (sym, sym') ->
        let mid_name = "mid_" ^ (show_symbol srk sym) in
        let mid_symbol =
          mk_symbol srk ~name:mid_name (typ_symbol srk sym)
        in
        let mid = mk_const srk mid_symbol in
        (Symbol.Map.add sym' mid subst1,
         Symbol.Map.add sym mid subst2))
      (Symbol.Map.empty, Symbol.Map.empty)
      (TF.symbols tf)
  in
  let seq = (* T(x,x_mid) /\ T(x_mid,x') *)
    let rename = (* rename Skolem constants *)
      Memo.memo (fun symbol ->
          mk_const srk (mk_symbol srk (typ_symbol srk symbol)))
    in
    (* substitution for first iteration *)
    let subst1 symbol =
      if Symbol.Map.mem symbol map' then
        Symbol.Map.find symbol map'
      else if TF.exists tf symbol then
        mk_const srk symbol
      else rename symbol
    in
    mk_and srk [substitute_const srk subst1 (TF.formula tf);
                substitute_map srk map (TF.formula tf)]
  in
  let solver = Smt.mk_solver srk in
  let models = ref [] in
  Smt.Solver.add solver [seq];
  let is_invariant p =
    let inv = mk_if srk (substitute_map srk map' p) (substitute_map srk map p) in
    List.for_all (fun m -> Interpretation.evaluate_formula m inv) !models && begin
        Smt.Solver.push solver;
        Smt.Solver.add solver [mk_not srk inv];
        match Smt.Solver.get_model solver with
        | `Sat m ->
           Smt.Solver.pop solver 1;
           models := m::(!models);
           false
        | `Unsat ->
           Smt.Solver.pop solver 1;
           true
        | `Unknown ->
           Smt.Solver.pop solver 1;
           false
      end
  in
  if Smt.Solver.check solver [] = `Unsat then
    []
  else
    List.filter is_invariant predicates

let invariant_partition srk candidates tf =
  let tf = TF.linearize srk tf in
  let predicates =
    invariant_transition_predicates srk tf candidates
    |> BatArray.of_list
  in
  let solver = Smt.mk_solver srk in
  Smt.Solver.add solver [TF.formula tf];
  (* The predicate induce a parition of the transitions of T by
     their valuation of the predicates; find the cells of this
     partition *)
  let rec find_cells cells =
    Smt.Solver.push solver;
    match Smt.Solver.get_model solver with
    | `Sat m ->
       let cell =
         Array.map (Interpretation.evaluate_formula m) predicates
       in
       let cell_formula =
         List.mapi (fun i sat ->
             if sat then predicates.(i)
             else mk_not srk predicates.(i))
           (Array.to_list cell)
         |> mk_and srk
       in
       Smt.Solver.add solver [mk_not srk cell_formula];
       find_cells (cell_formula::cells)
    | `Unsat -> cells
    | `Unknown -> assert false (* to do *)
  in
  find_cells []

  (* Each cell is i, (pos_pred_indices, neg_pred_indices), cell_formula *)
let invariant_complex_partition srk candidates tf =
    let tf = TF.linearize srk tf in
    logf "linearized transition formula to be partitioned: %a" (Formula.pp srk) (TF.formula tf);
    let predicates =
      invariant_transition_predicates srk tf candidates
      |> BatArray.of_list
    in
    let solver = Smt.mk_solver srk in
    Smt.Solver.add solver [TF.formula tf];
    (* The predicate induce a parition of the transitions of T by
       their valuation of the predicates; find the cells of this
       partition *)
    let rec find_cells cells =
      Smt.Solver.push solver;
      match Smt.Solver.get_model solver with
      | `Sat m ->
        logf "transition formula SAT, finding cell";
         let cell =
           Array.map (Interpretation.evaluate_formula m) predicates
         in
         let new_cell = 
          BatList.fold_lefti (
            fun (true_preds, false_preds) i sat -> 
              if sat then (BatSet.Int.add i true_preds, false_preds)
              else (true_preds, BatSet.Int.add i false_preds))
              (BatSet.Int.empty, BatSet.Int.empty)
              (Array.to_list cell)
          in
         let new_cell_formula =
           List.mapi (fun i sat ->
               if sat then predicates.(i)
               else mk_not srk predicates.(i))
             (Array.to_list cell)
           |> mk_and srk
         in
         logf "adding cell: %a" (Formula.pp srk) new_cell_formula;
         Smt.Solver.add solver [mk_not srk new_cell_formula];
         find_cells ((new_cell, new_cell_formula)::cells) 
      | `Unsat -> 
        logf "transition formula UNSAT, no further cells";
        cells
      | `Unknown -> assert false (* to do *)
    in
    predicates, find_cells []
  
(*  Ranked cells is a map from int to (list of sets), where int is the number of 
    positive predicates.
*)
let rank_cells cells =
  let ranked_cells = BatMap.Int.empty in
  BatList.fold_lefti
    (fun m i ((positive_preds, negative_preds), f) -> 
      let num_pos_preds = BatSet.Int.cardinal positive_preds in
      match BatMap.Int.find_opt num_pos_preds m with 
      | Some l -> BatMap.Int.update num_pos_preds num_pos_preds ((i, (positive_preds, negative_preds), f)::l) m
      | None -> BatMap.Int.add num_pos_preds [(i, (positive_preds, negative_preds), f)] m
    )
  ranked_cells
  cells

let build_graph_and_compute_mp srk tf inv_predicates omega_algebra ranked_cells num_cells =
  (* map' sends primed vars to midpoints; map sends unprimed vars to midpoints *)
  logf "start building phase transition graph";
  let (map', map) =
  List.fold_left (fun (subst1, subst2) (sym, sym') ->
      let mid_name = "mid_" ^ (show_symbol srk sym) in
      let mid_symbol =
        mk_symbol srk ~name:mid_name (typ_symbol srk sym)
      in
      let mid = mk_const srk mid_symbol in
      (Symbol.Map.add sym' mid subst1,
      Symbol.Map.add sym mid subst2))
    (Symbol.Map.empty, Symbol.Map.empty)
    (TF.symbols tf)
  in
  let seq = (* T(x,x_mid) /\ T(x_mid,x') *)
    let rename = (* rename Skolem constants *)
      Memo.memo (fun symbol ->
          mk_const srk (mk_symbol srk (typ_symbol srk symbol)))
    in
    (* substitution for first iteration *)
    let subst1 symbol =
      if Symbol.Map.mem symbol map' then
        Symbol.Map.find symbol map'
      else if TF.exists tf symbol then
        mk_const srk symbol
      else rename symbol
    in
    mk_and srk [substitute_const srk subst1 (TF.formula tf);
                substitute_map srk map (TF.formula tf)]
  in
  let indicators = 
    BatArray.mapi (fun ind pred -> 
      let indicator_name_px = "ind_1_for_pred_" ^ (string_of_int ind) in  
      let indicator_symbol = mk_symbol srk ~name:indicator_name_px `TyBool in       
      let predicate_clause = (* p(x, x_mid) *) substitute_map srk map' pred in
      let clause_1 = mk_iff srk (mk_const srk indicator_symbol) predicate_clause in
      let indicator_name_px' = "ind_2_for_pred_" ^ (string_of_int ind) in  
      let indicator_symbol' = mk_symbol srk ~name:indicator_name_px' `TyBool in       
      let predicate_clause' = (* p(x_mid, x') *) substitute_map srk map' pred in
      let clause_2 = mk_iff srk (mk_const srk indicator_symbol') predicate_clause' in
      mk_and srk [clause_1; clause_2]
      )
    inv_predicates
    |> BatArray.to_list
  in
  let phi = mk_and srk (seq::indicators) in 
  let solver = Smt.mk_solver srk in
  let models = ref [] in
  Smt.Solver.add solver [phi];

  let can_follow cell1 cell2 solver models =
    let cell1_pos, cell1_neg = cell1 in
    let cell2_pos, cell2_neg = cell2 in
    BatSet.Int.subset cell1_pos cell2_pos && 
    begin
      let cond_pos_clause = 
        (BatSet.Int.to_list cell1_pos)
        |>  BatList.map (fun ind -> 
              let indicator_name_px = "ind_1_for_pred_" ^ (string_of_int ind) in  
              let indicator_symbol = mk_symbol srk ~name:indicator_name_px `TyBool in 
              mk_const srk indicator_symbol
            ) 
        |> mk_and srk 
      in 
      let cond_neg_clause = 
        (BatSet.Int.to_list cell1_neg)
        |>  BatList.map (fun ind -> 
              let indicator_name_px = "ind_1_for_pred_" ^ (string_of_int ind) in  
              let indicator_symbol = mk_symbol srk ~name:indicator_name_px `TyBool in 
              mk_not srk (mk_const srk indicator_symbol)
            ) 
        |> mk_and srk 
      in 
      let new_pos_inds = BatSet.Int.diff cell2_pos cell1_pos in 
      let result_pos_clause = 
        (BatSet.Int.to_list new_pos_inds)
        |>  BatList.map (fun ind -> 
              let indicator_name_px = "ind_2_for_pred_" ^ (string_of_int ind) in  
              let indicator_symbol = mk_symbol srk ~name:indicator_name_px `TyBool in 
              mk_const srk indicator_symbol
            ) 
        |> mk_and srk 
      in 
      let result_neg_clause = 
        (BatSet.Int.to_list cell2_neg)
        |>  BatList.map (fun ind -> 
              let indicator_name_px = "ind_2_for_pred_" ^ (string_of_int ind) in  
              let indicator_symbol = mk_symbol srk ~name:indicator_name_px `TyBool in 
              mk_not srk (mk_const srk indicator_symbol)
            ) 
        |> mk_and srk 
      in 
      let cell2_can_follow_cell1 = mk_and srk [cond_neg_clause; cond_pos_clause; result_neg_clause; result_pos_clause] in
      List.exists (fun m -> Interpretation.evaluate_formula m cell2_can_follow_cell1) !models || 
      begin
        (* use the Solver.check to avoid pushing and popping, pass in a list of boolean vars *)
        Smt.Solver.push solver;
        Smt.Solver.add solver [cell2_can_follow_cell1];
        match Smt.Solver.get_model solver with
        | `Sat m ->
           Smt.Solver.pop solver 1;
           models := m::(!models);
           true
        | `Unsat ->
           Smt.Solver.pop solver 1;
           false
        | `Unknown ->
           Smt.Solver.pop solver 1;
           true
      end
    end
  in
  let module E = LinearRecurrenceInequation in
  let star tf = 
    let k = mk_symbol srk `TyInt in   
    let exists x = x != k && (TF.exists tf) x in
      TF.make ~exists (E.exp srk (TF.symbols tf) (mk_const srk k) (E.abstract srk tf)) (TF.symbols tf)
  in
  let algebra = WG.{
    mul = TF.mul srk;
    add = TF.add srk;
    one = TF.identity srk (TF.symbols tf);
    zero = TF.zero srk (TF.symbols tf);
    star = star
  } 
  in
  let wg = ref (WG.empty algebra) in
  (* node 0 as the virtual entry *)
  wg := WG.add_vertex !wg 0;
  (* virtual entry -> every cell with 0 indegree: weight 1
      self-loop for every cell: weight tf /\ cell_formula
      edge from cell A to cell B: weight 1
   *)
  let combine tf f = TF.make ~exists:(TF.exists tf) (mk_and srk [TF.formula tf; f]) (TF.symbols tf) in
  let zero_indegree_vertices = ref (BatSet.Int.empty) in
  logf "printing cell structure";
  BatMap.Int.iter (fun level cell_list ->
    logf "level %d: ========" level;
    BatList.iter (fun (cell_ind, (_, _), cell_formula) ->
      begin
        let restricted_tf = combine tf cell_formula in
        logf "adding cell %d as node %d with self-loop %a" (cell_ind) (cell_ind+1) (Formula.pp srk) (TF.formula restricted_tf) ;
        wg := WG.add_edge 
        !wg 
        (cell_ind+1) 
        restricted_tf
        (cell_ind+1);
        zero_indegree_vertices := BatSet.Int.add (cell_ind+1) !zero_indegree_vertices;
      end
       )
    cell_list
    )
  ranked_cells;
  let levels = BatArray.of_enum (BatMap.Int.keys ranked_cells) in
  let ancestors = BatArray.make num_cells BatSet.Int.empty in
  let descendants = BatArray.make num_cells BatSet.Int.empty in
  for current_level_idx = 1 to (BatArray.length levels) - 1 do 
    let current_level = levels.(current_level_idx) in
    logf "current level = %d" current_level;
    let targets = BatMap.Int.find current_level ranked_cells in
    for prev_level_idx = current_level_idx - 1 downto 0 do 
      let prev_level = levels.(prev_level_idx) in
      logf "previous level = %d" prev_level;
      let sources = BatMap.Int.find prev_level ranked_cells in 
      BatList.iter (fun (i, (pos_preds_i, neg_preds_i), cell_formula_i) -> 
        begin
          BatList.iter (fun (j, (pos_preds_j, neg_preds_j), _) -> 
            begin
            logf "checking if cell %d could be followed by cell %d" i j;
            if not (BatSet.Int.mem j (descendants.(i))) then
              logf "j is not one of i's descendants, check if i -> j";
              if can_follow (pos_preds_i, neg_preds_i) (pos_preds_j, neg_preds_j) solver models then 
                begin
                  logf "cell %d could be followed by cell %d" i j;
                  (* Cell # i is the (i+1)-th vertex in the graph *)
                  wg := WG.add_edge !wg (i+1) (combine tf cell_formula_i) (j+1);
                  zero_indegree_vertices := BatSet.Int.remove (j+1) !zero_indegree_vertices;
                  (* Adding i and i's ancestors into j's ancestors set *)
                  logf "updating ancestors and predecessors";
                  let i_ancestors = ancestors.(i) in
                  let j_ancestors = BatSet.Int.union ancestors.(j) i_ancestors in
                  BatArray.set ancestors j (BatSet.Int.add i j_ancestors);
                  (* Adding j to all its ancestors' descendants sets *)
                  BatSet.Int.iter (fun k -> 
                    let descendants_of_k = descendants.(k) in
                    BatArray.set descendants k (BatSet.Int.add j descendants_of_k); 
                    )
                  ancestors.(j);
                end
              end
          ) 
          targets
        end
      )
      sources;
    done;
  done;
  BatSet.Int.iter (
    fun v -> 
      logf "adding edge between virtual start and %d" v; 
      wg := WG.add_edge !wg 0 algebra.one v;
  ) 
  !zero_indegree_vertices;
  WG.omega_path_weight !wg omega_algebra 0
  
let compute_mp_with_phase_DAG srk candidate_predicates tf omega_algebra =
  let invariant_predicates, cells = invariant_complex_partition srk candidate_predicates tf in 
  logf "number of cells: %d" (List.length cells);
  List.iteri (
    fun i ((_, _), cell_formula) -> 
      logf "cell %d: %a" i (Formula.pp srk) cell_formula
  ) 
  cells;
  logf "invariant partition completed";
  let ranked_cells = rank_cells cells in 
  logf "cell ranking completed";
  build_graph_and_compute_mp srk tf invariant_predicates omega_algebra ranked_cells (List.length cells)
  
module InvariantDirection (Iter : PreDomain) = struct
  type 'a t = 'a Iter.t list list

  let pp srk tr_symbols formatter phases =
    let pp_phase formatter phase =
      Format.fprintf formatter "  @[<v 0>%a@]"
        (SrkUtil.pp_print_enum (Iter.pp srk tr_symbols)) (BatList.enum phase)
    in
    Format.fprintf formatter "Phases@. @[<v 0>%a@]"
      (SrkUtil.pp_print_enum pp_phase) (BatList.enum phases)

  let abstract srk tf =
    let tf = TF.linearize srk tf in
    let tr_symbols = TF.symbols tf in
    let exists = TF.exists tf in
    (* Use variable directions as candidate transition invariants *)
    let predicates =
      List.concat (List.map (fun (x,x') ->
          let x = mk_const srk x in
          let x' = mk_const srk x' in
          [mk_lt srk x x';
           mk_lt srk x' x;
           mk_eq srk x x'])
        tr_symbols)
      |> invariant_transition_predicates srk tf
      |> BatArray.of_list
    in
    let solver = Smt.mk_solver srk in
    Smt.Solver.add solver [TF.formula tf];
    (* The predicate induce a parition of the transitions of T by
       their valuation of the predicates; find the cells of this
       partition *)
    let rec find_cells cells =
      Smt.Solver.push solver;
      match Smt.Solver.get_model solver with
      | `Sat m ->
         let cell =
           Array.map (Interpretation.evaluate_formula m) predicates
         in
         let cell_formula =
           List.mapi (fun i sat ->
               if sat then predicates.(i)
               else mk_not srk predicates.(i))
             (Array.to_list cell)
           |> mk_and srk
         in
         Smt.Solver.add solver [mk_not srk cell_formula];
         find_cells (cell::cells)
      | `Unsat -> cells
      | `Unknown -> assert false (* to do *)
    in
    (* # of true predicates.  Since they're invariant, transitions
       belonging to a low-weight cell must precede transitions from
       higher-weight cells, and cells with equal weight can't appear
       in an execution *)
    let compare_weight cell1 cell2 =
      let weight cell =
        Array.fold_left (fun i v -> if v then i+1 else i) 0 cell
      in
      compare (weight cell1) (weight cell2)
    in
    BatList.sort compare_weight (find_cells [])
    |> BatList.group_consecutive (fun x y -> compare_weight x y = 0)
    |> List.map (List.map (fun cell ->
                     let cell_predicates =
                       BatArray.fold_lefti
                         (fun ps i v ->
                           if v then predicates.(i)::ps
                           else mk_not srk predicates.(i)::ps)
                         []
                         cell
                     in
                     let tf' =
                       TF.make
                         ~exists
                         (mk_and srk ((TF.formula tf)::cell_predicates))
                         tr_symbols
                     in
                     Iter.abstract srk tf'))

  let exp srk tr_symbols k phases =
    let exp_group mid_symbols k cells =
      let subst =
        BatList.fold_left2 (fun m (x, x') (sym, sym') ->
            Symbol.Map.add sym (mk_const srk x)
              (Symbol.Map.add sym' (mk_const srk x') m))
          Symbol.Map.empty
          mid_symbols
          tr_symbols
      in
      List.map (fun cell_iter ->
          Iter.exp srk tr_symbols k cell_iter
          |> substitute_map srk subst)
        cells
      |> mk_or srk
    in
    let rec go groups tr_symbols exp_formulas loop_counters =
      match groups with
      | [ ] ->
         (* formula is unsat *)
         assert (loop_counters == []);
         assert (exp_formulas == []);
         ([TF.formula (TF.identity srk tr_symbols)],
          [mk_real srk QQ.zero])
      | [x] ->
         let k = mk_const srk (mk_symbol srk ~name:"k" `TyInt) in
         ((exp_group tr_symbols k x)::exp_formulas,
          k::loop_counters)
      | (x::xs) ->
         let mid =
           List.map (fun (sym, _) ->
               let name = "mid_" ^ (show_symbol srk sym) in
               mk_symbol srk ~name:name (typ_symbol srk sym))
             tr_symbols
         in
         let tr_symbols1 =
           BatList.map2 (fun (sym, _) sym' -> (sym, sym')) tr_symbols mid
         in
         let tr_symbols2 =
           BatList.map2 (fun sym (_, sym') -> (sym, sym')) mid tr_symbols
         in
         let k = mk_const srk (mk_symbol srk ~name:"k" `TyInt) in
         go xs tr_symbols2 ((exp_group tr_symbols1 k x)::exp_formulas) (k::loop_counters)
    in
    let (formulas, loop_counters) =
      go phases tr_symbols [] []
    in
    mk_and srk (mk_eq srk k (mk_add srk loop_counters)::formulas)
end
