open Syntax
open BatPervasives
open Apak

include Log.Make(struct let name = "ark.iteration" end)

module V = Linear.QQVector
module QQMatrix = Linear.QQMatrix

type 'a iter =
  { ark : 'a context;
    symbols : (symbol * symbol) list;
    precondition : 'a Cube.t;
    postcondition : 'a Cube.t;
    stratified : (symbol * symbol * 'a term) list;
    inequations : ('a term * [ `Leq | `Eq ] * 'a term * 'a term) list }

let pp_iter formatter iter =
  let ark = iter.ark in
  Format.fprintf formatter
    "{@[<v 0>pre symbols:@;  @[<v 0>%a@]@;post symbols:@;  @[<v 0>%a@]@;"
    (ApakEnum.pp_print_enum (pp_symbol ark)) (BatList.enum iter.symbols /@ fst)
    (ApakEnum.pp_print_enum (pp_symbol ark)) (BatList.enum iter.symbols /@ snd);
  Format.fprintf formatter "pre:@;  @[<v 0>%a@]@;post:@;  @[<v 0>%a@]@;"
    Cube.pp iter.precondition
    Cube.pp iter.postcondition;
  Format.fprintf formatter
    "recurrences:@;  @[<v 0>%a@;%a@]}"
    (ApakEnum.pp_print_enum_nobox
       ~pp_sep:(fun formatter () -> Format.pp_print_break formatter 0 0)
       (fun formatter (sym', sym, incr) ->
          Format.fprintf formatter "%a = %a + %a"
            (pp_symbol ark) sym'
            (pp_symbol ark) sym
            (Term.pp ark) incr))
    (BatList.enum iter.stratified)
    (ApakEnum.pp_print_enum_nobox
       ~pp_sep:(fun formatter () -> Format.pp_print_break formatter 0 0)
       (fun formatter (post, op, pre, incr) ->
          Format.fprintf formatter "(%a) %s (%a) + %a"
            (Term.pp ark) post
            (match op with
             | `Eq -> "="
             | `Leq -> "<=")
            (Term.pp ark) pre
            (Term.pp ark) incr))
    (BatList.enum iter.inequations)

let abstract_iter_cube ark cube tr_symbols =
  let pre_symbols =
    List.fold_left (fun set (s,_) ->
        Symbol.Set.add s set)
      Symbol.Set.empty
      tr_symbols
  in
  let post_symbols =
    List.fold_left (fun set (_,s') ->
        Symbol.Set.add s' set)
      Symbol.Set.empty
      tr_symbols
  in
(*
  let is_symbolic_constant x =
    not (Symbol.Set.mem x pre_symbols || Symbol.Set.mem x post_symbols)
  in
*)
  let precondition =
    Cube.exists (not % flip Symbol.Set.mem post_symbols) cube
  in
  let postcondition =
    Cube.exists (not % flip Symbol.Set.mem pre_symbols) cube
  in
  let (stratified, non_induction) =
    let equalities = Cube.farkas_equalities cube in
    let coeff_vec =
      List.fold_left (fun map (term, vec) ->
          match Term.destruct ark term with
          | `App (sym, []) -> Symbol.Map.add sym vec map
          | _ -> map)
        Symbol.Map.empty
        equalities
    in
    let eq_table = ExprHT.create 991 in
    List.iter (fun (term, vec) -> ExprHT.add eq_table term vec) equalities;
    (* Matrix consisting of one row for each pre/post symbol, which contains
       the coefficient vector for that symbol *)
    let matrix =
      Symbol.Set.fold (fun sym m ->
          let sym_coeff =
            try
              Symbol.Map.find sym coeff_vec
            with Not_found -> V.zero
          in
          QQMatrix.add_row (int_of_symbol sym) sym_coeff m)
        (Symbol.Set.union pre_symbols post_symbols)
        QQMatrix.zero
    in
    let rec go induction non_induction tail matrix =
      match non_induction with
      | [] -> (List.rev induction, tail)
      | (sym,sym')::non_induction ->
        (* coefficient of sym' must be -1, coefficent of sym must be 1 *)
        let diff =
          V.add_term
            (QQ.of_int (-1))
            (int_of_symbol sym')
            (V.of_term QQ.one (int_of_symbol sym))
        in
        match Linear.solve matrix diff with
        | Some solution ->
          (* Add sym to induction vars *)
          let induction =
            let rhs =
              let sym_term = mk_const ark sym in
              let sym'_term = mk_const ark sym' in
              BatList.filter_map (fun (term, coeff) ->
                  if Term.equal term sym_term || Term.equal term sym'_term then
                    None
                  else
                    Some (mk_mul ark [mk_real ark (V.dot coeff solution); term]))
                equalities
              |> mk_add ark
            in
            (sym', sym, rhs)::induction
          in
          (* Remove sym row from the matrix.  sym' row stays to ensure that
             recurrences are only over pre-state variables. *)
          let (_, matrix) = QQMatrix.pivot (int_of_symbol sym) matrix in
          go induction (non_induction@tail) [] matrix
        | None ->
          go induction non_induction ((sym,sym')::tail) matrix
    in
    go [] tr_symbols [] matrix
  in
  let inequations =

    (* For every non-induction var x, substitute x -> x' - x in the loop body;
       the project out all post-variables.  In the resulting cube, the var
       x should be interpreted as the difference x'-x. *)
    let post_map =
      (* map from non-induction pre-state vars to their post-state
         counterparts *)
      List.fold_left
        (fun map (sym, sym') -> Symbol.Map.add sym sym' map)
        Symbol.Map.empty
        non_induction
    in
    let postify =
      let subst sym =
        if Symbol.Map.mem sym post_map then
          mk_const ark (Symbol.Map.find sym post_map)
        else
          mk_const ark sym
      in
      substitute_const ark subst
    in
    let diff_cube =
      let delta_subst sym =
        if Symbol.Map.mem sym post_map then
          (* non-induction var *)
          mk_add ark [mk_const ark (Symbol.Map.find sym post_map);
                      mk_neg ark (mk_const ark sym)]
        else
          mk_const ark sym
      in
      let rewrite = substitute_const ark delta_subst in
      (* don't allow delta vars as subterms *)
      let subterm sym = not (Symbol.Map.mem sym post_map) in
      Cube.to_atoms cube
      |> List.map rewrite
      |> Cube.of_atoms ark
      |> Cube.exists ~subterm (not % flip Symbol.Set.mem post_symbols)
    in

    let zero_term = mk_real ark QQ.zero in
    (* try to rewrite a term as (delta_term + term) where delta_term contains
       only delta vars and term contains no delta vars *)
    let alg = function
      | `App (sym, []) ->
        if Symbol.Map.mem sym post_map then
          Some (mk_const ark sym, zero_term)
        else
          Some (zero_term, mk_const ark sym)
      | `Real k ->
        Some (zero_term, mk_real ark k)
      | `Add xs ->
        Some (mk_add ark (List.map fst xs), mk_add ark (List.map snd xs))
      | `Mul xs ->
        let mul x (lhs', rhs') =
          match x with
          | None -> None
          | Some (lhs, rhs) ->
            if Term.equal lhs zero_term then
              if Term.equal lhs' zero_term then
                Some (zero_term, mk_mul ark [rhs; rhs'])
              else
                match Term.destruct ark rhs with
                | `Real _ -> Some (mk_mul ark [rhs; lhs'], mk_mul ark [rhs; rhs'])
                | _ -> None
            else if Term.equal lhs' zero_term then
              match Term.destruct ark rhs' with
              | `Real _ -> Some (mk_mul ark [rhs'; lhs], mk_mul ark [rhs'; rhs])
              | _ -> None
            else
              None
        in
        List.fold_left mul (Some (List.hd xs)) (List.tl xs)
      | `Binop (`Div, (lhs,rhs), (lhs',rhs')) ->
        if Term.equal lhs' zero_term then
          if Term.equal lhs zero_term then
            Some (zero_term, mk_div ark rhs rhs')
          else
            match Term.destruct ark rhs' with
            | `Real _ -> Some (mk_div ark lhs rhs', mk_div ark rhs rhs')
            | _ -> None
        else
          None
      | `Binop (`Mod, (lhs,rhs), (lhs',rhs')) ->
        if Term.equal lhs' zero_term && Term.equal lhs zero_term then
          Some (zero_term, mk_mod ark rhs rhs')
        else
          None
      | `Unop (`Floor, (lhs,rhs)) ->
        if Term.equal lhs zero_term then
          Some (zero_term, mk_floor ark rhs)
        else
          None
      | `Unop (`Neg, (lhs,rhs)) ->
        Some (mk_neg ark lhs, mk_neg ark rhs)
      | `App (_, _) | `Ite (_, _, _) | `Var (_, _) -> None
    in
    let recur atom =
      match Interpretation.destruct_atom ark atom with
      | `Comparison (op, s, t) ->
        let op = match op with
          | `Leq -> `Leq
          | `Lt -> `Leq
          | `Eq -> `Eq
        in
        BatOption.bind
          (Term.eval_partial ark alg (mk_sub ark s t))
          (fun (lhs, rhs) ->
             if Term.equal lhs zero_term then
               None
             else
               Some (postify lhs, op, lhs, mk_neg ark rhs))
      | `Literal (_, _) -> None
    in
    BatList.filter_map recur (Cube.to_atoms diff_cube)
  in
  { ark;
    symbols = tr_symbols;
    precondition;
    postcondition;
    stratified;
    inequations }


module QQUvp = Polynomial.QQUvp
module IntMap = Apak.Putil.PInt.Map
module Cf = struct
  type 'a t = ('a, typ_arith, QQUvp.t) ExprMap.t

  let zero = ExprMap.empty

  let enum = ExprMap.enum
  
  let k_minus_1 = QQUvp.add_term QQ.one 1 (QQUvp.scalar (QQ.of_int (-1)))

  (* Compose a closed form with a uvp *)
  let compose cf p =
    ExprMap.filter_map
      (fun _ coeff ->
         let coeff' = QQUvp.compose coeff p in
         if QQUvp.is_zero coeff' then
           None
         else
           Some coeff')
      cf

  let add u v =
    let f _ a b =
      match a, b with
      | Some a, Some b ->
        let sum = QQUvp.add a b in
        if QQUvp.is_zero sum then None else Some sum
      | Some x, None | None, Some x -> Some x
      | None, None -> assert false
    in
    ExprMap.merge f u v

  let add_term coeff dim vec =
    if QQUvp.is_zero coeff then vec else begin
      try
        let sum = QQUvp.add coeff (ExprMap.find dim vec) in
        if not (QQUvp.is_zero sum) then ExprMap.add dim sum vec
        else ExprMap.remove dim vec
      with Not_found -> ExprMap.add dim coeff vec
    end

  let term coeff dim = add_term coeff dim zero

  let const ark uvp = add_term uvp (mk_real ark QQ.one) zero

  let of_enum enum =
    BatEnum.fold (fun t (dim, coeff) -> add_term coeff dim t) zero enum
  
  let mul ark u v =
    ApakEnum.cartesian_product
      (enum u)
      (enum v)
    /@ (fun ((xdim, xcoeff), (ydim, ycoeff)) ->
        (mk_mul ark [xdim; ydim], QQUvp.mul xcoeff ycoeff))
    |> of_enum

  let scalar_mul scalar vec =
    if QQUvp.is_zero scalar then
      zero
    else
      ExprMap.map (QQUvp.mul scalar) vec

  exception Quit
  
  (* Lower a degree-0 cf to a regular term *)
  let term_of_0 ark cf =
    try
      let lowered =
        enum cf
        /@ (fun (dim, coeff) ->
            let (const_coeff, higher_order) = QQUvp.pivot 0 coeff in
            if QQUvp.equal higher_order QQUvp.zero then
              mk_mul ark [mk_real ark const_coeff; dim]
            else
              raise Quit)
        |> BatList.of_enum
        |> mk_add ark
      in
      Some lowered
    with Quit -> None

  let of_term ark env =
    let rec alg = function
      | `App (v, []) ->
        begin
          match env v with
          | Some cf -> Some (compose cf k_minus_1)
          | None -> None
        end
      | `App (func, args) ->
        begin
          match BatOption.bind (env func) (term_of_0 ark) with
          | None -> None
          | Some t ->
            begin match Term.destruct ark t with
              | `App (func', []) when func = func' ->
                let args' =
                  BatList.filter_map
                    (fun arg ->
                       match refine ark arg with
                       | `Term t ->
                         BatOption.bind (Term.eval_partial ark alg t) (term_of_0 ark)
                       | `Formula _ -> None)
                    args
                in
                if List.length args = List.length args' then
                  Some (term QQUvp.one (mk_app ark func args'))
                else
                  None
              | _ -> None
            end
        end
      | `Real k -> Some (const ark (QQUvp.scalar k))
      | `Add xs -> Some (List.fold_left add zero xs)
      | `Mul [] -> Some (const ark (QQUvp.scalar QQ.one))
      | `Mul (x::xs) -> Some (List.fold_left (mul ark) x xs)
      | `Binop (`Div, x, y) ->
        (* to do: if denomenator is a constant then the numerator can be loop dependent *)
        begin match term_of_0 ark x, term_of_0 ark y with
          | Some x, Some y -> Some (term QQUvp.one (mk_div ark x y))
          | _, _ -> None
        end
      | `Binop (`Mod, x, y) ->
        begin match term_of_0 ark x, term_of_0 ark y with
          | Some x, Some y -> Some (term QQUvp.one (mk_mod ark x y))
          | _, _ -> None
        end
      | `Unop (`Floor, x) ->
        begin match term_of_0 ark x with
          | Some x -> Some (term QQUvp.one (mk_floor ark x))
          | None -> None
        end
      | `Unop (`Neg, x) -> Some (scalar_mul (QQUvp.negate QQUvp.one) x)
      | `Ite (_, _, _) -> None
      | `Var (_, _) -> None
    in
    Term.eval_partial ark alg

  let summation cf =
    (* QQUvp.summation computes q(n) = sum_{i=0}^n p(i); shift to compute
       q(n) = sum_{i=1}^n p(i) *)
    let sum_from_1 px =
      QQUvp.add_term (QQ.negate (QQUvp.eval px QQ.zero)) 0 (QQUvp.summation px)
    in
    ExprMap.map sum_from_1 cf
  
  (* Convert a closed form into a term by instantiating the variable in the
     polynomial coefficients of the closed form *)
  let term_of ark cf k =
    let polynomial_term px =
      QQUvp.enum px
      /@ (fun (coeff, order) ->
          mk_mul ark
            ((mk_real ark coeff)::(BatList.of_enum ((1 -- order) /@ (fun _ -> k)))))
      |> BatList.of_enum
      |> mk_add ark
    in
    enum cf
    /@ (fun (term, px) -> mk_mul ark [term; polynomial_term px])
    |> BatList.of_enum
    |> mk_add ark
end

let abstract_iter ?(exists=fun x -> true) ark phi symbols =
  let tr_symbols =
    List.fold_left (fun set (s,s') ->
        Symbol.Set.add s (Symbol.Set.add s' set))
      Symbol.Set.empty
      symbols
  in
  let subterm x = not (Symbol.Set.mem x tr_symbols) in
  let cube = 
    Abstract.abstract_nonlinear ~exists ark phi
    |> Cube.exists ~subterm (fun _ -> true)
  in
  abstract_iter_cube ark cube symbols

let closure (iter : 'a iter) : 'a formula =
  let loop_counter_sym = mk_symbol iter.ark ~name:"K" `TyInt in
  let loop_counter = mk_const iter.ark loop_counter_sym in

  (* In a recurrence environment, absence of a binding for a variable
     indicates that the variable is not modified (i.e., the variable satisfies
     the recurrence x' = x + 0).  We initialize the environment to bind None
     to each modified variable. *)
  let induction_vars =
    BatList.fold_left
      (fun iv (s,s') ->
         Symbol.Map.add s None
           (Symbol.Map.add s' None iv))
      Symbol.Map.empty
      iter.symbols
  in
  (* Substitute variables on a term with their closed forms, then find the
     closed form for the summation sum_{i=0}^loop_counter rhs(i) *)
  let close_sum induction_vars rhs =
    let env sym =
      if Symbol.Map.mem sym induction_vars then
        Symbol.Map.find sym induction_vars
      else
        Some (Cf.term QQUvp.one (mk_const iter.ark sym))
    in
    Cf.of_term iter.ark env rhs
    |> BatOption.map Cf.summation
  in

  (* Close all stratified recurrence equations *)
  let induction_vars =
    List.fold_left (fun induction_vars (_, sym, rhs) ->
        match close_sum induction_vars rhs with
        | Some close_rhs ->
          let cf =
            Cf.add_term QQUvp.one (mk_const iter.ark sym) close_rhs
          in
          Symbol.Map.add sym (Some cf) induction_vars
        | None ->
          logf ~level:`warn "Failed to find closed form for %a"
            (pp_symbol iter.ark) sym;
          induction_vars)
      induction_vars
      iter.stratified
  in

  let stratified =
    BatList.filter_map (fun (sym,sym') ->
        Symbol.Map.find sym induction_vars
        |> BatOption.map (fun cf ->
            mk_eq iter.ark
              (mk_const iter.ark sym')
              (Cf.term_of iter.ark cf loop_counter)))
      iter.symbols
    |> mk_and iter.ark
  in

  let inequations =
    BatList.filter_map (fun (post, op, pre, incr) ->
        match close_sum induction_vars incr with
        | None -> None
        | Some cf ->
          let rhs = mk_add iter.ark [pre; Cf.term_of iter.ark cf loop_counter] in
          match op with
          | `Leq -> Some (mk_leq iter.ark post rhs)
          | `Eq -> Some (mk_eq iter.ark post rhs))
      iter.inequations
    |> mk_and iter.ark
  in
  let zero_iter =
    List.map (fun (sym, sym') ->
        mk_eq iter.ark (mk_const iter.ark sym) (mk_const iter.ark sym'))
      iter.symbols
    |> mk_and iter.ark
  in

  mk_or iter.ark [
    zero_iter;
    mk_and iter.ark [
      Cube.to_formula iter.precondition;
      mk_leq iter.ark (mk_real iter.ark QQ.one) loop_counter;
      stratified;
      inequations;
      Cube.to_formula iter.postcondition
    ]
  ]

let cube_of_iter iter =
  let eq_constraints =
    iter.stratified |> List.map (fun (post, pre, incr) ->
        mk_eq iter.ark
          (mk_const iter.ark post)
          (mk_add iter.ark [mk_const iter.ark pre; incr]))
  in
  let ineq_constraints =
    iter.inequations |> List.map (fun (post, op, pre, incr) ->
        let rhs =
          mk_add iter.ark [pre; incr]
        in
        match op with
        | `Eq -> mk_eq iter.ark post rhs
        | `Leq -> mk_leq iter.ark post rhs)
  in
  let postcondition = Cube.to_atoms iter.postcondition in
  let precondition = Cube.to_atoms iter.precondition in
  Cube.of_atoms
    iter.ark
    (eq_constraints@ineq_constraints@postcondition@precondition)

let equal iter iter' =
  Cube.equal (cube_of_iter iter) (cube_of_iter iter')

let widen iter iter' =
  let body = Cube.widen (cube_of_iter iter) (cube_of_iter iter') in
  assert(iter.symbols = iter'.symbols);
  abstract_iter_cube iter.ark body iter.symbols

let join iter iter' =
  let body =
    Cube.join (cube_of_iter iter) (cube_of_iter iter')
  in
  assert(iter.symbols = iter'.symbols);
  abstract_iter_cube iter.ark body iter.symbols

let star ?(exists=fun x -> true) ark phi symbols =
  closure (abstract_iter ~exists ark phi symbols)
