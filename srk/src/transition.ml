open Syntax
open BatPervasives

include Log.Make(struct let name = "srk.transition" end)

module type Var = sig
  type t
  val pp : Format.formatter -> t -> unit
  val show : t -> string
  val typ : t -> [ `TyInt | `TyReal ]
  val compare : t -> t -> int
  val symbol_of : t -> symbol
  val of_symbol : symbol -> t option
end

module Make
    (C : sig
       type t
       val context : t context
     end)
    (Var : Var) =
struct
  module M = BatMap.Make(Var)

  type var = Var.t

  type t =
    { transform : (C.t term) M.t;
      guard : C.t formula }

  let compare x y =
    match Formula.compare x.guard y.guard with
    | 0 -> M.compare Term.compare x.transform y.transform
    | cmp -> cmp

  let srk = C.context

  let pp formatter tr =
    Format.fprintf formatter "{@[<v 0>";
    SrkUtil.pp_print_enum_nobox
       ~pp_sep:(fun formatter () -> Format.pp_print_break formatter 0 0)
       (fun formatter (lhs, rhs) ->
          Format.fprintf formatter "%a := @[%a@]"
            Var.pp lhs
            (Term.pp srk) rhs)
       formatter
       (M.enum tr.transform);
    begin match Formula.destruct srk tr.guard with
      | `Tru -> ()
      | _ ->
        if not (M.is_empty tr.transform) then
          Format.pp_print_break formatter 0 0;
        Format.fprintf formatter "when @[<v 0>%a@]" (Formula.pp srk) tr.guard
    end;
    Format.fprintf formatter "@]}"

  let show = SrkUtil.mk_show pp

  let construct guard assignment =
    { transform =
        List.fold_left (fun m (v, term) -> M.add v term m) M.empty assignment;
      guard = guard }

  let assign v term =
    { transform = M.add v term M.empty;
      guard = mk_true srk }

  let parallel_assign assignment = construct (mk_true srk) assignment

  let assume guard = construct guard []

  let havoc vars =
    let transform =
      List.fold_left (fun transform v ->
          M.add
            v
            (mk_const srk (mk_symbol srk ~name:"havoc" (Var.typ v :> typ)))
            transform)
        M.empty
        vars
    in
    { transform = transform; guard = mk_true srk }

  let mul left right =
    let fresh_skolem =
      Memo.memo (fun sym ->
          let name = show_symbol srk sym in
          let typ = typ_symbol srk sym in
          mk_const srk (mk_symbol srk ~name typ))
    in
    let left_subst sym =
      match Var.of_symbol sym with
      | Some var ->
        if M.mem var left.transform then
          M.find var left.transform
        else
          mk_const srk sym
      | None -> fresh_skolem sym
    in
    let guard =
      mk_and srk [left.guard;
                  substitute_const srk left_subst right.guard]
    in
    let transform =
      M.fold (fun var term transform ->
          if M.mem var transform then
            transform
          else
            M.add var term transform)
        left.transform
        (M.map (substitute_const srk left_subst) right.transform)
    in
    { transform; guard }

  let add left right =
    let left_eq = ref [] in
    let right_eq = ref [] in
    let transform =
      let merge v x y =
        match x, y with
        | Some s, Some t when Term.equal s t -> Some s
        | _, _ ->
          let phi =
            mk_symbol srk ~name:("phi_" ^ (Var.show v)) ((Var.typ v) :> typ)
            |> mk_const srk
          in
          let left_term =
            match x with
            | Some s -> s
            | None -> mk_const srk (Var.symbol_of v)
          in
          let right_term =
            match y with
            | Some t -> t
            | None -> mk_const srk (Var.symbol_of v)
          in
          left_eq := (mk_eq srk left_term phi)::(!left_eq);
          right_eq := (mk_eq srk right_term phi)::(!right_eq);
          Some phi
      in
      M.merge merge left.transform right.transform
    in
    let guard =
      mk_or srk [mk_and srk (left.guard::(!left_eq));
                 mk_and srk (right.guard::(!right_eq))]
    in
    { guard; transform }

  (* Canonical names for post-state symbols.  Having canonical names
     simplifies equality testing and widening. *)
  let post_symbol =
    Memo.memo (fun sym ->
        match Var.of_symbol sym with
        | Some var ->
          mk_symbol srk ~name:(Var.show var ^ "'") (Var.typ var :> typ)
        | None -> assert false)

  let to_transition_formula tr =
    let (tr_symbols, post_def) =
      M.fold (fun var term (symbols, post_def) ->
          let pre_sym = Var.symbol_of var in
          let post_sym = post_symbol pre_sym in
          let post_term = mk_const srk post_sym in
          ((pre_sym,post_sym)::symbols,
           (mk_eq srk post_term term)::post_def))
        tr.transform
        ([], [])
    in
    let body =
      mk_and srk (tr.guard::post_def)
      |> rewrite srk
        ~up:(SrkSimplify.simplify_terms_rewriter srk % Nonlinear.simplify_terms_rewriter srk)
    in
    let exists =
      let post_symbols =
        List.fold_left
          (fun set (_, sym') -> Symbol.Set.add sym' set)
          Symbol.Set.empty
          tr_symbols
      in
      fun x ->
      match Var.of_symbol x with
      | Some _ -> true
      | None -> Symbol.Set.mem x post_symbols
    in
    TransitionFormula.make ~exists body tr_symbols

  let domain =
    let open Iteration in
    let open SolvablePolynomial in
    ref (module ProductWedge(SolvablePolynomial)(WedgeGuard) : PreDomain)

  let star tr =
    let (module D) = !domain in
    let tf = to_transition_formula tr in
    let iter = D.abstract srk tf in
    let tr_symbols = TransitionFormula.symbols tf in
    let transform =
      List.fold_left (fun tr (pre, post) ->
          match Var.of_symbol pre with
          | Some v -> M.add v (mk_const srk post) tr
          | None -> assert false)
        M.empty
        tr_symbols
    in
    let loop_counter_sym = mk_symbol srk ~name:"K" `TyInt in
    let loop_counter = mk_const srk loop_counter_sym in
    let closure =
      mk_and srk [D.exp srk tr_symbols loop_counter iter;
                  mk_leq srk (mk_real srk QQ.zero) loop_counter]
    in
    { transform = transform;
      guard = closure }

  let zero =
    { transform = M.empty; guard = mk_false srk }

  let one =
    { transform = M.empty; guard = mk_true srk }

  let is_zero tr =
    match Formula.destruct srk tr.guard with
    | `Fls -> true
    | _ -> false

  let is_one tr =
    match Formula.destruct srk tr.guard with
    | `Tru -> M.is_empty tr.transform
    | _ -> false

  let widen x y =
    (* Introduce fresh symbols for variables in the transform of x/y, then
       abstract x and y to a wedge over pre-symbols and these fresh symbols.
       Widen in the wedge domain, then covert back to a formula. *)
    let (transform, post_sym) =
      let add (map, post) var =
        if M.mem var map then
          (map, post)
        else
          let name = Var.show var ^ "'" in
          let sym = mk_symbol srk ~name (Var.typ var :> typ) in
          (M.add var (mk_const srk sym) map, Symbol.Set.add sym post)
      in
      BatEnum.fold
        add
        (BatEnum.fold add (M.empty, Symbol.Set.empty) (M.keys y.transform))
        (M.keys x.transform)
    in
    let exists sym =
      match Var.of_symbol sym with
      | Some _ -> true
      | None -> Symbol.Set.mem sym post_sym
    in
    let to_wedge z =
      let eqs =
        M.fold (fun var term eqs ->
            let term' =
              if M.mem var z.transform then
                M.find var z.transform
              else
                mk_const srk (Var.symbol_of var)
            in
            (mk_eq srk term term')::eqs)
          transform
          []
      in
      mk_and srk (z.guard::eqs)
      |> Wedge.abstract ~exists srk
    in
    let guard =
      Wedge.widen (to_wedge x) (to_wedge y)
      |> Wedge.to_formula
    in
    { transform; guard }

  let widen x y =
    if is_zero x then y
    else if is_zero y then x
    else widen x y

  (* alpha equivalence - only works for normalized transitions! *)
  exception Not_normal
  let equiv x y =
    let sigma =
      let map =
        M.fold (fun v rhs m ->
            match Term.destruct srk rhs,
                  Term.destruct srk (M.find v y.transform) with
            | `App (a, []), `App (b, []) -> Symbol.Map.add a (mk_const srk b) m
            | _ -> raise Not_normal)
          x.transform
          Symbol.Map.empty
      in
      fun sym ->
        try Symbol.Map.find sym map
        with Not_found -> mk_const srk sym
    in
    let x_guard = substitute_const srk sigma x.guard in
    let equiv = SrkSimplify.simplify_terms srk (mk_iff srk x_guard y.guard) in
    match Wedge.is_sat srk (mk_not srk equiv) with
    | `Unsat -> true
    | _ -> false

  let equiv x y =
    try equiv x y
    with | Not_found -> false
         | Not_normal -> false

  let equal x y =
    compare x y = 0
    || is_zero x && (Smt.is_sat srk y.guard) = `Unsat
    || is_zero y && (Smt.is_sat srk x.guard) = `Unsat
    || equiv x y

  let exists p tr =
    let transform = M.filter (fun k _ -> p k) tr.transform in
    let rename =
      Memo.memo (fun sym ->
          mk_symbol srk ~name:(show_symbol srk sym) (typ_symbol srk sym))
    in
    let sigma sym =
      let sym' = match Var.of_symbol sym with
        | Some v -> if p v then sym else rename sym
        | None -> sym
      in
      mk_const srk sym'
    in
    { transform = M.map (substitute_const srk sigma) transform;
      guard = substitute_const srk sigma tr.guard }

  let mem_transform x tr = M.mem x tr.transform
  let get_transform x tr = M.find x tr.transform
  let transform tr = M.enum tr.transform
  let guard tr = tr.guard

  let interpolate trs post =
    let trs =
      trs |> List.map (fun tr ->
          let fresh_skolem =
            Memo.memo (fun sym ->
                match Var.of_symbol sym with
                | Some _ -> mk_const srk sym
                | None ->
                  let name = show_symbol srk sym in
                  let typ = typ_symbol srk sym in
                  mk_const srk (mk_symbol srk ~name typ))
          in
          { transform = M.map (substitute_const srk fresh_skolem) tr.transform;
            guard = substitute_const srk fresh_skolem tr.guard })
    in
    let unsubscript_tbl = Hashtbl.create 991 in
    let subscript_tbl = Hashtbl.create 991 in
    let subscript sym =
      try
        Hashtbl.find subscript_tbl sym
      with Not_found -> mk_const srk sym
    in
    let unsubscript sym =
      try
        Hashtbl.find unsubscript_tbl sym
      with Not_found -> mk_const srk sym
    in
    (* Convert tr into a formula, and simultaneously update the subscript
       table *)
    let to_ss_formula tr =
      let (ss, phis) =
        M.fold (fun var term (ss, phis) ->
            let var_sym = Var.symbol_of var in
            let var_ss_sym = mk_symbol srk (Var.typ var :> typ) in
            let var_ss_term = mk_const srk var_ss_sym in
            let term_ss = substitute_const srk subscript term in
            Hashtbl.add unsubscript_tbl var_ss_sym (mk_const srk var_sym);
            ((var_sym, var_ss_term)::ss,
             mk_eq srk var_ss_term term_ss::phis))
          tr.transform
          ([], [substitute_const srk subscript tr.guard])
      in
      List.iter (fun (k, v) -> Hashtbl.add subscript_tbl k v) ss;
      mk_and srk phis
    in
    let seq =
      List.fold_left
        (fun subscripted tr ->
           (to_ss_formula tr)::subscripted)
        []
        trs
    in
    let ss_post = substitute_const srk subscript (mk_not srk post) in
    match SrkZ3.interpolate_seq srk (List.rev (ss_post::seq)) with
    | `Sat _ -> `Invalid
    | `Unknown -> `Unknown
    | `Unsat itp ->
      `Valid (List.map (substitute_const srk unsubscript) itp)

  let valid_triple phi path post =
    let path_not_post = List.fold_right mul path (assume (mk_not srk post)) in
    match Smt.is_sat srk (mk_and srk [phi; path_not_post.guard]) with
    | `Sat -> `Invalid
    | `Unknown -> `Unknown
    | `Unsat -> `Valid

  let defines tr =
    M.fold
      (fun var _ defs -> var::defs)
      tr.transform
      []

  let uses tr =
    M.fold
      (fun _ term uses ->
         Symbol.Set.union (symbols term) uses)
      tr.transform
      (symbols tr.guard)
    |> Symbol.Set.enum
    |> BatEnum.filter_map Var.of_symbol
    |> BatList.of_enum

  let abstract_post pre tr =
    let srk = C.context in
    let man = SrkApron.get_manager pre in
    let exists x = Var.of_symbol x != None in
    let fresh =
      Memo.memo (fun sym -> mk_const srk (mk_symbol srk (typ_symbol srk sym)))
    in
    let tr_subst expr =
      substitute_const srk (fun sym ->
          match Var.of_symbol sym with
          | Some v when mem_transform v tr -> fresh sym
          | _ -> mk_const srk sym)
        expr
    in
    let transform_formula =
      transform tr
      /@ (fun (lhs, rhs) ->
          (mk_eq srk (mk_const srk (Var.symbol_of lhs)) (tr_subst rhs)))
      |> BatList.of_enum
    in
    mk_and srk ((tr_subst (SrkApron.formula_of_property pre))
                :: (tr_subst tr.guard)
                :: transform_formula)
    |> Nonlinear.linearize srk
    |> rewrite srk ~down:(nnf_rewriter srk)
    |> Abstract.abstract ~exists srk man

  let linearize tr =
    let (transform, defs) =
      M.fold (fun var t (transform, defs) ->
          let (pure_t, t_defs) =
            SrkSimplify.purify srk (Nonlinear.uninterpret srk t)
          in
          let new_defs =
            Symbol.Map.enum t_defs
            /@ (fun (v,t) ->
              match Expr.refine srk t with
              | `Term t ->
                 mk_eq srk (mk_const srk v) (Nonlinear.interpret srk t)
              | _ -> assert false)
            |> BatList.of_enum
          in
          (M.add var pure_t transform, new_defs@defs))
        tr.transform
        (M.empty, [])
    in
    let guard =
      Nonlinear.linearize srk (mk_and srk (tr.guard::defs))
    in
    { transform; guard }
end
