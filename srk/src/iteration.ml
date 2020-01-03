open Syntax
open BatPervasives

include Log.Make(struct let name = "srk.iteration" end)

module V = Linear.QQVector
module CS = CoordinateSystem

module type PreDomain = sig
  type 'a t
  val pp : 'a context -> (symbol * symbol) list -> Format.formatter -> 'a t -> unit
  val exp : 'a context -> (symbol * symbol) list -> 'a term -> 'a t -> 'a formula
  val join : 'a context -> (symbol * symbol) list -> 'a t -> 'a t -> 'a t
  val widen : 'a context -> (symbol * symbol) list -> 'a t -> 'a t -> 'a t
  val equal : 'a context -> (symbol * symbol) list -> 'a t -> 'a t -> bool
  val abstract : ?exists:(symbol -> bool) ->
    'a context ->
    (symbol * symbol) list ->
    'a formula ->
    'a t
end

module type PreDomainWedge = sig
  include PreDomain
  val abstract_wedge : 'a context -> (symbol * symbol) list -> 'a Wedge.t -> 'a t
end

module type Domain = sig
  type 'a t
  val pp : Format.formatter -> 'a t -> unit
  val closure : 'a t -> 'a formula
  val join : 'a t -> 'a t -> 'a t
  val widen : 'a t -> 'a t -> 'a t
  val equal : 'a t -> 'a t -> bool
  val abstract : ?exists:(symbol -> bool) ->
    'a context ->
    (symbol * symbol) list ->
    'a formula ->
    'a t
  val tr_symbols : 'a t -> (symbol * symbol) list
end

let identity srk tr_symbols =
  List.map (fun (sym, sym') ->
      mk_eq srk (mk_const srk sym) (mk_const srk sym'))
    tr_symbols
  |> mk_and srk

let pre_symbols tr_symbols =
  List.fold_left (fun set (s,_) ->
      Symbol.Set.add s set)
    Symbol.Set.empty
    tr_symbols

let post_symbols tr_symbols =
  List.fold_left (fun set (_,s') ->
      Symbol.Set.add s' set)
    Symbol.Set.empty
    tr_symbols

(* Map from pre-state vars to their post-state counterparts *)
let post_map srk tr_symbols =
  List.fold_left
    (fun map (sym, sym') -> Symbol.Map.add sym (mk_const srk sym') map)
    Symbol.Map.empty
    tr_symbols

module WedgeGuard = struct
  type 'a t =
    { precondition : 'a Wedge.t;
      postcondition : 'a Wedge.t }

  let pp _ _ formatter iter =
    Format.fprintf formatter "pre:@;  @[<v 0>%a@]@;post:@;  @[<v 0>%a@]"
      Wedge.pp iter.precondition
      Wedge.pp iter.postcondition

  let abstract_wedge _ tr_symbols wedge =
    let pre_symbols = pre_symbols tr_symbols in
    let post_symbols = post_symbols tr_symbols in
    let precondition =
      Wedge.exists (not % flip Symbol.Set.mem post_symbols) wedge
    in
    let postcondition =
      Wedge.exists (not % flip Symbol.Set.mem pre_symbols) wedge
    in
    { precondition; postcondition }

  let abstract ?(exists=fun _ -> true) srk tr_symbols phi =
    let post_symbols = post_symbols tr_symbols in
    let subterm x = not (Symbol.Set.mem x post_symbols) in
    let wedge =
      Wedge.abstract ~exists ~subterm srk phi
    in
    abstract_wedge srk tr_symbols wedge

  let exp srk tr_symbols loop_counter guard =
    mk_or srk [mk_and srk [mk_eq srk loop_counter (mk_real srk QQ.zero);
                           identity srk tr_symbols];
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

  let abstract ?(exists=fun _ -> true) srk tr_symbols phi =
    let phi = Nonlinear.linearize srk phi in
    let phi =
      rewrite srk ~down:(nnf_rewriter srk) phi
    in
    let post_symbols = post_symbols tr_symbols in
    let pre_symbols = pre_symbols tr_symbols in
    let man = Polka.manager_alloc_strict () in
    let precondition =
      let exists x =
        exists x && not (Symbol.Set.mem x post_symbols)
      in
      Abstract.abstract ~exists srk man phi
    in
    let postcondition =
      let exists x =
        exists x && not (Symbol.Set.mem x pre_symbols)
      in
      Abstract.abstract ~exists srk man phi
    in
    { precondition; postcondition }

  let exp srk tr_symbols loop_counter guard =
    mk_or srk [mk_and srk [mk_eq srk loop_counter (mk_real srk QQ.zero);
                           identity srk tr_symbols];
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

  let abstract ?(exists=fun _ -> true) srk tr_symbols phi =
    let phi =
      rewrite srk ~up:(abstract_presburger_rewriter srk) phi
    in
    let phi =
      rewrite srk ~down:(nnf_rewriter srk) phi
    in
    let pre_symbols = pre_symbols tr_symbols in
    let post_symbols = post_symbols tr_symbols in
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
                           identity srk tr_symbols];
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

  let abstract ?exists:(_ = fun _ -> true) srk tr_symbols phi =
    let phi = rewrite srk ~down:(nnf_rewriter srk) phi in
    let phi = Nonlinear.linearize srk phi in
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

  let equal _ _ _ _ = failwith "Not yet implemented"
  let join _ _ _ _ = failwith "Not yet implemented"
  let widen _ _ _ _ = failwith "Not yet implemented"
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

  let join srk tr_symbols (a, b) (a', b') =
    (A.join srk tr_symbols a a', B.join srk tr_symbols b b')

  let widen srk tr_symbols (a, b) (a', b') =
    (A.widen srk tr_symbols a a', B.widen srk tr_symbols b b')

  let equal srk tr_symbols (a, b) (a', b') =
    (A.equal srk tr_symbols a a')
    && (B.equal srk tr_symbols b b')

  let abstract ?(exists=fun _ -> true) srk tr_symbols phi =
    (A.abstract ~exists srk tr_symbols phi,
     B.abstract ~exists srk tr_symbols phi)
end

module Sum (A : PreDomain) (B : PreDomain) () = struct
  type 'a t = Left of 'a A.t | Right of 'a B.t

  let abstract_left = ref true

  let pp srk tr_symbols formatter = function
    | Left a -> A.pp srk tr_symbols formatter a
    | Right b -> B.pp srk tr_symbols formatter b

  let left a = Left a

  let right b = Right b

  let exp srk tr_symbols loop_counter = function
    | Left a -> A.exp srk tr_symbols loop_counter a
    | Right b -> B.exp srk tr_symbols loop_counter b

  let join srk tr_symbols x y = match x,y with
    | Left x, Left y -> Left (A.join srk tr_symbols x y)
    | Right x, Right y -> Right (B.join srk tr_symbols x y)
    | _, _ -> invalid_arg "Join: incompatible elements"

  let widen srk tr_symbols x y = match x,y with
    | Left x, Left y -> Left (A.widen srk tr_symbols x y)
    | Right x, Right y -> Right (B.widen srk tr_symbols x y)
    | _, _ -> invalid_arg "Widen: incompatible elements"

  let equal srk tr_symbols x y = match x,y with
    | Left x, Left y -> A.equal srk tr_symbols x y
    | Right x, Right y -> B.equal srk tr_symbols x y
    | _, _ -> invalid_arg "Equal: incompatible elements"

  let abstract ?(exists=fun _ -> true) srk tr_symbols phi =
    if !abstract_left then
      Left (A.abstract ~exists srk tr_symbols phi)
    else
      Right (B.abstract ~exists srk tr_symbols phi)
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

  (* Lower a split iter into an iter by picking an arbitary split and joining
     both sides. *)
  let lower_split srk tr_symbols split_iter =
    match BatEnum.get (Expr.Map.values split_iter) with
    | Some (iter, iter') -> Iter.join srk tr_symbols iter iter'
    | None -> assert false

  let base_bottom srk tr_symbols = Iter.abstract srk tr_symbols (mk_false srk)

  let lift_split srk tr_symbols iter =
    Expr.Map.add
      (mk_true srk)
      (iter, base_bottom srk tr_symbols)
      Expr.Map.empty

  let abstract ?(exists=fun _ -> true) srk tr_symbols body =
    let post_symbols = post_symbols tr_symbols in
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
    let post_map = post_map srk tr_symbols in
    let postify =
      let subst sym =
        if Symbol.Map.mem sym post_map then
          Symbol.Map.find sym post_map
        else
          mk_const srk sym
      in
      substitute_const srk subst
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
          let left_abstract =
            Iter.abstract ~exists srk tr_symbols not_psi_body
          in
          let right_abstract =
            Iter.abstract ~exists srk tr_symbols psi_body
          in
          Expr.Map.add not_psi (left_abstract, right_abstract) split_iter
        else if sat_modulo_body (mk_and srk [not_psi; post_psi]) = `Unsat then
          (* {not phi} body {not phi} -> body* = ([phi]body)*([not phi]body)* *)
          let left_abstract =
            Iter.abstract ~exists srk tr_symbols psi_body
          in
          let right_abstract =
            Iter.abstract ~exists srk tr_symbols not_psi_body
          in
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
          (Iter.abstract ~exists srk tr_symbols body,
           base_bottom srk tr_symbols)
          Expr.Map.empty
      else
        split_iter
    in
    split_iter

  let sequence srk symbols phi psi =
    let (phi_map, psi_map) =
      List.fold_left (fun (phi_map, psi_map) (sym, sym') ->
          let mid_name = "mid_" ^ (show_symbol srk sym) in
          let mid_symbol =
            mk_symbol srk ~name:mid_name (typ_symbol srk sym)
          in
          let mid = mk_const srk mid_symbol in
          (Symbol.Map.add sym' mid phi_map,
           Symbol.Map.add sym mid psi_map))
        (Symbol.Map.empty, Symbol.Map.empty)
        symbols
    in
    let phi_subst symbol =
      if Symbol.Map.mem symbol phi_map then
        Symbol.Map.find symbol phi_map
      else
        mk_const srk symbol
    in
    let psi_subst symbol =
      if Symbol.Map.mem symbol psi_map then
        Symbol.Map.find symbol psi_map
      else
        mk_const srk symbol
    in
    mk_and srk [substitute_const srk phi_subst phi;
                substitute_const srk psi_subst psi]

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
          sequence srk tr_symbols left_closure right_closure
        in
        mk_and srk [left_right;
                    mk_eq srk (mk_add srk [left_counter; right_counter]) loop_counter])
    |> BatList.of_enum
    |> mk_and srk

  let join srk tr_symbols split_iter split_iter' =
    let f _ a b = match a,b with
      | Some (a_left, a_right), Some (b_left, b_right) ->
        Some (Iter.join srk tr_symbols a_left b_left,
              Iter.join srk tr_symbols a_right b_right)
      | _, _ -> None
    in
    let split_join = Expr.Map.merge f split_iter split_iter' in
    if Expr.Map.is_empty split_join then
      lift_split srk tr_symbols
        (Iter.join srk tr_symbols
           (lower_split srk tr_symbols split_iter)
           (lower_split srk tr_symbols split_iter'))
    else
      split_join

  let widen srk tr_symbols split_iter split_iter' =
    let f _ a b = match a,b with
      | Some (a_left, a_right), Some (b_left, b_right) ->
        Some (Iter.widen srk tr_symbols a_left b_left,
              Iter.widen srk tr_symbols a_right b_right)
      | _, _ -> None
    in
    let split_widen = Expr.Map.merge f split_iter split_iter' in
    if Expr.Map.is_empty split_widen then
      lift_split srk tr_symbols
        (Iter.widen srk tr_symbols
           (lower_split srk tr_symbols split_iter)
           (lower_split srk tr_symbols split_iter))
    else
      split_widen

  let equal srk tr_symbols split_iter split_iter' =
    BatEnum.for_all
      (fun ((p,(l,r)), (p',(l',r'))) ->
         Formula.equal p p'
         && Iter.equal srk tr_symbols l l'
         && Iter.equal srk tr_symbols r r')
      (BatEnum.combine
         (Expr.Map.enum split_iter,
          Expr.Map.enum split_iter'))
end

module MakeDomain (Iter : PreDomain) = struct
  type 'a t =
    { srk : 'a context;
      tr_symbols : (symbol * symbol) list;
      iter : 'a Iter.t }

  let equal iter iter' =
    let srk = iter.srk in
    let tr_symbols = iter.tr_symbols in
    iter.tr_symbols = iter'.tr_symbols
    && Iter.equal srk tr_symbols iter.iter iter'.iter

  let join iter iter' =
    let srk = iter.srk in
    let tr_symbols = iter.tr_symbols in
    assert(iter.tr_symbols = iter'.tr_symbols);
    let iter = Iter.join srk tr_symbols iter.iter iter'.iter in
    { srk; tr_symbols; iter }

  let widen iter iter' =
    let srk = iter.srk in
    let tr_symbols = iter.tr_symbols in
    assert(iter.tr_symbols = iter'.tr_symbols);
    let iter = Iter.widen srk tr_symbols iter.iter iter'.iter in
    { srk; tr_symbols; iter }

  let pp formatter iter =
    Format.fprintf formatter "{@[<v 1>%a@]}"
      (Iter.pp iter.srk iter.tr_symbols) iter.iter

  let closure iter =
    let srk = iter.srk in
    let loop_counter_sym = mk_symbol srk ~name:"K" `TyInt in
    let loop_counter = mk_const srk loop_counter_sym in
    mk_and srk [Iter.exp iter.srk iter.tr_symbols loop_counter iter.iter;
                mk_leq srk (mk_real srk QQ.zero) loop_counter]

  let abstract ?(exists=fun _ -> true) srk tr_symbols body =
    let iter = Iter.abstract ~exists srk tr_symbols body in
    { srk; tr_symbols; iter }

  let tr_symbols iter = iter.tr_symbols
end

module ProductWedge (A : PreDomainWedge) (B : PreDomainWedge) = struct
  include Product(A)(B)

  let abstract_wedge srk tr_symbols wedge =
    (A.abstract_wedge srk tr_symbols wedge,
     B.abstract_wedge srk tr_symbols wedge)

  let abstract ?(exists=fun _ -> true) srk tr_symbols phi =
    let post_symbols = post_symbols tr_symbols in
    let subterm x = not (Symbol.Set.mem x post_symbols) in
    let wedge = Wedge.abstract ~exists ~subterm srk phi in
    abstract_wedge srk tr_symbols wedge
end

module SumWedge (A : PreDomainWedge) (B : PreDomainWedge) () = struct
  include Sum(A)(B)()

  let abstract_wedge srk tr_symbols wedge =
    if !abstract_left then
      Left (A.abstract_wedge srk tr_symbols wedge)
    else
      Right (B.abstract_wedge srk tr_symbols wedge)
end
