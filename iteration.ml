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
    stratified : (symbol * 'a term) list;
    inequations : ('a term * [ `Leq | `Eq ] * 'a term) list }

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
       (fun formatter (lhs, rhs) ->
          Format.fprintf formatter "%a' = %a + %a"
            (pp_symbol ark) lhs
            (pp_symbol ark) lhs
            (Term.pp ark) rhs))
    (BatList.enum iter.stratified)
    (ApakEnum.pp_print_enum_nobox
       ~pp_sep:(fun formatter () -> Format.pp_print_break formatter 0 0)
       (fun formatter (lhs, op, rhs) ->
          Format.fprintf formatter "(%a)' %s (%a) + %a"
            (Term.pp ark) lhs
            (match op with
             | `Eq -> "="
             | `Leq -> "<=")
            (Term.pp ark) lhs
            (Term.pp ark) rhs))
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
  let stratified =
    let equalities = Cube.farkas_equalities cube in
    let coeff_vec =
      List.fold_left (fun map (term, vec) ->
          match Term.destruct ark term with
          | `Const sym -> Symbol.Map.add sym vec map
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
      | [] -> List.rev induction
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
            (sym, rhs)::induction
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
    []
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
      | `Const v | `App (v, []) ->
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
              | `Const func' when func = func' ->
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

  let summation cf = ExprMap.map QQUvp.summation cf
  
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
    List.fold_left (fun induction_vars (sym, rhs) ->
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

  mk_and iter.ark
    [Cube.to_formula iter.precondition;
     stratified;
     Cube.to_formula iter.postcondition]

let star ?(exists=fun x -> true) ark phi symbols =
  closure (abstract_iter ~exists ark phi symbols)
