open Syntax
open BatPervasives
open Apak

include Log.Make(struct let name = "ark.iteration" end)

module V = Linear.QQVector
module QQMatrix = Linear.QQMatrix

module ExprVec = Linear.ExprQQVector

module QQUvp = Polynomial.QQUvp
module Cf = struct
  include Linear.MakeExprRingMap(QQUvp)

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
        (* to do: if denomenator is a constant then the numerator can be loop
           dependent *)
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

(*    x'    <=       (3 * x) +  y + 1
      --    --        -         -----
   exp_lhs exp_op exp_coeff    exp_add *)
type 'a exponential =
  { exp_lhs : 'a term;
    exp_op : [ `Leq | `Eq | `Geq ];
    exp_coeff : QQ.t;
    exp_rhs : 'a term;
    exp_add : 'a term }



type 'a iter =
  { ark : 'a context;
    symbols : (symbol * symbol) list;
    precondition : 'a Cube.t;
    postcondition : 'a Cube.t;
    stratified : (symbol * symbol * 'a term) list;
    inequations : ('a term * [ `Leq | `Eq ] * 'a term * 'a term) list;
    exponential : ('a exponential) list }

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
    "recurrences:@;  @[<v 0>%a@;%a@;%a@]@]}"
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
    (ApakEnum.pp_print_enum_nobox
       ~pp_sep:(fun formatter () -> Format.pp_print_break formatter 0 0)
       (fun formatter { exp_lhs; exp_op; exp_coeff; exp_rhs; exp_add } ->
          Format.fprintf formatter "(%a) %s %a * (%a) + %a"
            (Term.pp ark) exp_lhs
            (match exp_op with
             | `Eq -> "="
             | `Leq -> "<="
             | `Geq -> ">=")
            QQ.pp exp_coeff
            (Term.pp ark) exp_rhs
            (Term.pp ark) exp_add))
    (BatList.enum iter.exponential)

let show_iter x = Putil.mk_show pp_iter x

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
  let is_symbolic_constant x =
    not (Symbol.Set.mem x pre_symbols || Symbol.Set.mem x post_symbols)
  in
  let precondition =
    Cube.exists (not % flip Symbol.Set.mem post_symbols) cube
  in
  let postcondition =
    Cube.exists (not % flip Symbol.Set.mem pre_symbols) cube
  in
  let (stratified, non_induction) =
    let equalities = Cube.farkas_equalities cube in
    (* Matrix consisting of one row for each dimension of the cube that is
       associated with a term that contains a transition variable; the row
       contains the Farkas column for that dimension *)
    let matrix =
      BatList.fold_lefti (fun m id (term, column) ->
          if Symbol.Set.for_all is_symbolic_constant (symbols term) then
            m
          else
            QQMatrix.add_row id column m)
        QQMatrix.zero
        equalities
    in
    let row_of_symbol =
      BatList.fold_lefti (fun map id (term, _) ->
          match Term.destruct ark term with
          | `App (sym, []) -> Symbol.Map.add sym id map
          | _ -> map)
        Symbol.Map.empty
        equalities
    in
    let rec go induction non_induction tail matrix =
      match non_induction with
      | [] -> (List.rev induction, tail)
      | (sym,sym')::non_induction ->
        (* coefficient of sym' must be -1, coefficent of sym must be 1 *)
        let sym_row = Symbol.Map.find sym row_of_symbol in
        let diff =
          V.add_term
            (QQ.of_int (-1))
            (Symbol.Map.find sym' row_of_symbol)
            (V.of_term QQ.one sym_row)
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
             recurrences are only over pre-state variables.

             TODO: Should also filter out rows corresponding to terms
             involving only induction variables.  *)
          let (_, matrix) = QQMatrix.pivot sym_row matrix in
          go induction (non_induction@tail) [] matrix
        | None ->
          go induction non_induction ((sym,sym')::tail) matrix
    in
    (* Filter out transition symbols without associated rows in the matrix --
       those are not induction variables *)
    let non_induction =
      List.filter (fun (s,s') ->
          Symbol.Map.mem s row_of_symbol && Symbol.Map.mem s' row_of_symbol)
        tr_symbols
    in
    go [] non_induction [] matrix
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
  let exponential =
    BatList.enum non_induction
    /@ (fun (sym, sym') ->
        let subterm = is_symbolic_constant in
        let keep x =
          is_symbolic_constant x || x = sym || x = sym'
        in
        Cube.exists ~subterm keep cube
        |> Cube.to_atoms
        |> BatList.filter_map (fun atom ->
            match Interpretation.destruct_atom ark atom with
            | `Comparison (op, s, t) ->
              let recurrence = ExprVec.of_term ark (mk_sub ark s t) in
              begin
                try
                  let exp_lhs = mk_const ark sym' in
                  let sym_term = mk_const ark sym in
                  let rhs_coeff = ExprVec.coeff sym_term recurrence in
                  let lhs_coeff = ExprVec.coeff exp_lhs recurrence in
                  if QQ.equal lhs_coeff QQ.zero || QQ.equal rhs_coeff QQ.zero then
                    None
                  else
                    let exp_op =
                      match op with
                      | `Leq | `Lt when QQ.lt QQ.zero lhs_coeff -> `Leq
                      | `Leq | `Lt -> `Geq
                      | `Eq -> `Eq
                    in
                    let exp_add =
                      ExprMap.map
                        (fun k -> QQ.negate (QQ.div k lhs_coeff))
                        (ExprMap.add sym_term QQ.zero
                           (ExprMap.add exp_lhs QQ.zero recurrence))
                      |> ExprVec.term_of ark
                    in
                    let exp_coeff = QQ.negate (QQ.div rhs_coeff lhs_coeff) in
                    Some { exp_lhs;
                           exp_rhs = sym_term;
                           exp_add;
                           exp_coeff;
                           exp_op }
                with Not_found -> None
              end
            | `Literal (_, _) -> None))
    |> BatEnum.fold (@) []
  in
  { ark;
    symbols = tr_symbols;
    precondition;
    postcondition;
    stratified;
    inequations;
    exponential }


let abstract_iter ?(exists=fun x -> true) ark phi symbols =
  let post_symbols =
    List.fold_left (fun set (_,s') ->
        Symbol.Set.add s' set)
      Symbol.Set.empty
      symbols
  in
  let subterm x = not (Symbol.Set.mem x post_symbols) in
  let cube = 
    Abstract.abstract_nonlinear ~exists ark phi
    |> Cube.exists ~subterm (fun _ -> true)
  in
  abstract_iter_cube ark cube symbols

let closure ?(guard=None) (iter : 'a iter) : 'a formula =
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
  let guard = match guard with
    | None -> mk_true iter.ark
    | Some guard -> guard
  in
  mk_or iter.ark [
    zero_iter;
    mk_and iter.ark [
      Cube.to_formula iter.precondition;
      mk_leq iter.ark (mk_real iter.ark QQ.one) loop_counter;
      stratified;
      inequations;
      Cube.to_formula iter.postcondition;
      guard
    ]
  ]

exception No_translation
let closure_ocrs ?(guard=None) iter =
  let open Ocrs in
  let open Type_def in

  let pow =
    if not (is_registered_name iter.ark "pow") then
      register_named_symbol iter.ark "pow" (`TyFun ([`TyReal; `TyReal], `TyReal));
    get_named_symbol iter.ark "pow"
  in

  let loop_counter_sym = mk_symbol iter.ark ~name:"K" `TyInt in
  let loop_counter = mk_const iter.ark loop_counter_sym in

  let string_of_symbol = string_of_int % int_of_symbol in
  let symbol_of_string = symbol_of_int % int_of_string in

  let post_map = (* map pre-state vars to post-state vars *)
    List.fold_left (fun map (pre, post) ->
        Symbol.Map.add pre post map)
      Symbol.Map.empty
      iter.symbols
  in

  let pre_map = (* map post-state vars to pre-state vars *)
    List.fold_left (fun map (pre, post) ->
        Symbol.Map.add post pre map)
      Symbol.Map.empty
      iter.symbols
  in

  (* pre/post subscripts *)
  let ss_pre = SSVar "k" in
  let ss_post = SAdd ("k", 1) in

  let expr_of_term =
    let alg = function
      | `App (sym, []) ->
        if Symbol.Map.mem sym pre_map then
          (* sym is a post-state var -- replace it with pre-state var *)
          Output_variable (string_of_symbol (Symbol.Map.find sym pre_map),
                           ss_post)
        else if Symbol.Map.mem sym post_map then
          Output_variable (string_of_symbol sym,
                           ss_pre)
        else
          Symbolic_Constant (string_of_symbol sym)
      | `App (sym, _) -> assert false (* to do *)
      | `Real k -> Rational (Mpqf.to_mpq k)
      | `Add xs -> Sum xs
      | `Mul xs -> Product xs
      | `Binop (`Div, x, y) -> Divide (x, y)
      | `Unop (`Neg, x) -> Minus (Rational (Mpq.of_int 0), x)
      | `Binop (`Mod, _, _) | `Unop (`Floor, _) -> raise No_translation
      | `Ite (_, _, _) | `Var (_, _) -> assert false
    in
    Term.eval iter.ark alg
  in

  let rec term_of_expr = function
    | Plus (x, y) -> mk_add iter.ark [term_of_expr x; term_of_expr y]
    | Minus (x, y) -> mk_sub iter.ark (term_of_expr x) (term_of_expr y)
    | Times (x, y) -> mk_mul iter.ark [term_of_expr x; term_of_expr y]
    | Divide (x, y) -> mk_div iter.ark (term_of_expr x) (term_of_expr y)
    | Product xs -> mk_mul iter.ark (List.map term_of_expr xs)
    | Sum xs -> mk_add iter.ark (List.map term_of_expr xs)
    | Symbolic_Constant name -> mk_const iter.ark (symbol_of_string name)
    | Base_case (name, index) ->
      assert (index = 0);
      mk_const iter.ark (symbol_of_string name)
    | Input_variable name ->
      assert (name = "k");
      loop_counter
    | Output_variable (name, subscript) ->
      assert (subscript = ss_pre);
      Symbol.Map.find (symbol_of_string name) post_map
      |> mk_const iter.ark
    | Rational k -> mk_real iter.ark (Mpqf.of_mpq k)
    | Undefined -> assert false
    | Pow (x, Rational k) ->
      let base = term_of_expr x in
      begin
        match QQ.to_int (Mpqf.of_mpq k) with
        | Some k ->
          (1 -- k)
          /@ (fun _ -> base)
          |> BatList.of_enum
          |> mk_mul iter.ark
        | None -> assert false
      end
    | Pow (x, y) ->
      let base = term_of_expr x in
      let exp = term_of_expr y in
      mk_app iter.ark pow [base; exp]

    | Log (_, _) | Binomial (_, _) | Factorial _ -> assert false
  in

  let recurrences =
    let filter_map f xs =
      let g x =
        try Some (f x)
        with No_translation -> None
      in
      BatList.filter_map g xs
    in
    let stratified =
      filter_map (fun (post, pre, term) ->
          (Output_variable (string_of_symbol pre, ss_pre),
           Equals (Output_variable (string_of_symbol pre, ss_post),
                   Plus (Output_variable (string_of_symbol pre, ss_pre),
                         expr_of_term term))))
        iter.stratified
    in
    let inequations =
      (* $ is a placeholder variable that we use to avoid sending OCRS
         recurrences on terms *)
      filter_map (fun (post, op, pre, term) ->
          let lhs = Output_variable ("$", ss_post) in
          let rhs =
            Plus (Output_variable ("$", ss_pre),
                  expr_of_term term)
          in
          let ineq =
            match op with
            | `Eq -> Equals (lhs, rhs)
            | `Leq -> LessEq (lhs, rhs)
          in
          (expr_of_term post, ineq))
        iter.inequations
    in
    let exponential =
      (* $ is a placeholder variable that we use to avoid sending OCRS
         recurrences on terms *)
      List.map (fun { exp_lhs; exp_op; exp_coeff; exp_rhs; exp_add } ->
          let lhs = Output_variable ("$", ss_post) in
          let rhs =
            Plus (Product [Rational (Mpqf.to_mpq exp_coeff);
                           Output_variable ("$", ss_pre)],
                  expr_of_term exp_add)
          in
          let ineq =
            match exp_op with
            | `Eq -> Equals (lhs, rhs)
            | `Leq -> LessEq (lhs, rhs)
            | `Geq -> GreaterEq (lhs, rhs)
          in
          (expr_of_term exp_lhs, ineq))
        iter.exponential
    in
    stratified@inequations@exponential
  in
  let closed =
    let to_formula = function
      | Equals (x, y) -> mk_eq iter.ark (term_of_expr x) (term_of_expr y)
      | LessEq (x, y) -> mk_leq iter.ark (term_of_expr x) (term_of_expr y)
      | Less (x, y) -> mk_lt iter.ark (term_of_expr x) (term_of_expr y)
      | GreaterEq (x, y) -> mk_leq iter.ark (term_of_expr y) (term_of_expr x)
      | Greater (x, y) -> mk_lt iter.ark (term_of_expr y) (term_of_expr x)
    in
    List.map to_formula (Ocrs.solve_rec_list_pair recurrences)
  in
  let zero_iter =
    List.map (fun (sym, sym') ->
        mk_eq iter.ark (mk_const iter.ark sym) (mk_const iter.ark sym'))
      iter.symbols
    |> mk_and iter.ark
  in
  let guard = match guard with
    | None -> mk_true iter.ark
    | Some guard -> guard
  in
  mk_or iter.ark [
    zero_iter;
    mk_and iter.ark ([
        Cube.to_formula iter.precondition;
        mk_leq iter.ark (mk_real iter.ark QQ.one) loop_counter;
        Cube.to_formula iter.postcondition;
        guard
      ]@closed)
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
  let exponential_constraints =
    iter.exponential |> List.map (fun r ->
        let rhs =
          mk_add iter.ark [mk_mul iter.ark [mk_real iter.ark r.exp_coeff;
                                           r.exp_rhs];
                           r.exp_add]
        in
        match r.exp_op with
        | `Eq -> mk_eq iter.ark r.exp_lhs rhs
        | `Leq -> mk_leq iter.ark r.exp_lhs rhs
        | `Geq -> mk_leq iter.ark rhs r.exp_lhs)
  in
  let postcondition = Cube.to_atoms iter.postcondition in
  let precondition = Cube.to_atoms iter.precondition in
  Cube.of_atoms
    iter.ark
    (eq_constraints@ineq_constraints@exponential_constraints@postcondition@precondition)

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

let bottom ark symbols =
  { ark = ark;
    symbols = symbols;
    precondition = Cube.bottom ark;
    postcondition = Cube.bottom ark;
    stratified = [];
    inequations = [];
    exponential = [] }

let tr_symbols iter = iter.symbols

module Split = struct
  type 'a split_iter = ('a, typ_bool, ('a iter * 'a iter)) ExprMap.t

  let ark split_iter =
    match BatEnum.get (ExprMap.values split_iter) with
    | Some (iter, _) -> iter.ark
    | None -> assert false

  let tr_symbols split_iter =
    match BatEnum.get (ExprMap.values split_iter) with
    | Some (iter, _) -> iter.symbols
    | None -> assert false

  let pp_split_iter formatter split_iter =
    let pp_elt formatter (pred,(left,right)) =
      Format.fprintf formatter "[@[<v 0>%a@; %a@; %a@]]"
        (Formula.pp (ark split_iter)) pred
        pp_iter left
        pp_iter right
    in
    Format.fprintf formatter "<Split @[<v 0>%a@]>"
      (ApakEnum.pp_print_enum pp_elt) (ExprMap.enum split_iter)

  let show_split_iter x = Putil.mk_show pp_split_iter x

  (* Lower a split iter into an iter by picking an arbitary split and joining
     both sides. *)
  let lower_split split_iter =
    match BatEnum.get (ExprMap.values split_iter) with
    | Some (iter, iter') -> join iter iter'
    | None -> assert false

  let lift_split iter =
    ExprMap.add
      (mk_true iter.ark)
      (iter, bottom iter.ark iter.symbols)
      ExprMap.empty

  let abstract_iter ?(exists=fun x -> true) ark body tr_symbols =
    let post_symbols =
      List.fold_left (fun set (_,s') ->
          Symbol.Set.add s' set)
        Symbol.Set.empty
        tr_symbols
    in
    let predicates =
      let preds = ref ExprSet.empty in
      let prestate sym = exists sym && not (Symbol.Set.mem sym post_symbols) in
      let rr expr =
        match destruct ark expr with
        | `Not phi ->
          if Symbol.Set.for_all prestate (symbols phi) then
            preds := ExprSet.add phi (!preds);
          expr
        | `Atom (op, s, t) ->
          let phi =
            match op with
            | `Eq -> mk_eq ark s t
            | `Leq -> mk_leq ark s t
            | `Lt -> mk_lt ark s t
          in
          begin
          if Symbol.Set.for_all prestate (symbols phi) then
            let redundant = match op with
              | `Eq -> false
              | `Leq -> ExprSet.mem (mk_lt ark t s) (!preds)
              | `Lt -> ExprSet.mem (mk_lt ark t s) (!preds)
            in
            if not redundant then
              preds := ExprSet.add phi (!preds)
          end;
          expr
        | _ -> expr
      in
      ignore (rewrite ark ~up:rr body);
      BatList.of_enum (ExprSet.enum (!preds))
    in
    let uninterp_body =
      rewrite ark
        ~up:(Abstract.nonlinear_uninterpreted_rewriter ark)
        body
    in
    let solver = Smt.mk_solver ark in
    solver#add [uninterp_body];
    let sat_modulo_body psi =
      solver#push ();
      solver#add [psi];
      let result = solver#check [] in
      solver#pop 1;
      result
    in
    let is_split_predicate psi =
      (sat_modulo_body psi = `Sat)
      && (sat_modulo_body (mk_not ark psi) = `Sat)
    in
    let post_map =
      List.fold_left
        (fun map (s, s') ->
           Symbol.Map.add s (mk_const ark s') map)
        Symbol.Map.empty
        tr_symbols
    in
    let postify =
      let subst sym =
        if Symbol.Map.mem sym post_map then
          Symbol.Map.find sym post_map
        else
          mk_const ark sym
      in
      substitute_const ark subst
    in
    let add_split_predicate split_iter psi =
      if is_split_predicate psi then
        let not_psi = mk_not ark psi in
        let post_psi = postify psi in
        let post_not_psi = postify not_psi in
        let psi_body = mk_and ark [body; psi] in
        let not_psi_body = mk_and ark [body; not_psi] in
        if sat_modulo_body (mk_and ark [psi; post_not_psi]) = `Unsat then
          (* {psi} body {psi} -> body* = ([not psi]body)*([psi]body)* *)
          let left_abstract =
            abstract_iter ~exists ark not_psi_body tr_symbols
          in
          let right_abstract =
            abstract_iter ~exists ark psi_body tr_symbols
          in
          ExprMap.add not_psi (left_abstract, right_abstract) split_iter
        else if sat_modulo_body (mk_and ark [not_psi; post_psi]) = `Unsat then
          (* {not phi} body {not phi} -> body* = ([phi]body)*([not phi]body)* *)
          let left_abstract =
            abstract_iter ~exists ark psi_body tr_symbols
          in
          let right_abstract =
            abstract_iter ~exists ark not_psi_body tr_symbols
          in
          ExprMap.add psi (left_abstract, right_abstract) split_iter
        else
          split_iter
      else
        split_iter
    in
    let split_iter =
      List.fold_left add_split_predicate ExprMap.empty predicates
    in
    (* If there are no predicates that can split the loop, split on true *)
    let split_iter =
      if ExprMap.is_empty split_iter then
        ExprMap.add
          (mk_true ark)
          (abstract_iter ~exists ark body tr_symbols,
           bottom ark tr_symbols)
          ExprMap.empty
      else
        split_iter
    in
    logf "abstract: %a" (Formula.pp ark) body;
    logf "iter: %a" pp_split_iter split_iter;
    split_iter

  let sequence ark symbols phi psi =
    let (phi_map, psi_map) =
      List.fold_left (fun (phi_map, psi_map) (sym, sym') ->
          let mid_name = "mid_" ^ (show_symbol ark sym) in
          let mid_symbol =
            mk_symbol ark ~name:mid_name (typ_symbol ark sym)
          in
          let mid = mk_const ark mid_symbol in
          (Symbol.Map.add sym' mid phi_map,
           Symbol.Map.add sym mid psi_map))
        (Symbol.Map.empty, Symbol.Map.empty)
        symbols
    in
    let phi_subst symbol =
      if Symbol.Map.mem symbol phi_map then
        Symbol.Map.find symbol phi_map
      else
        mk_const ark symbol
    in
    let psi_subst symbol =
      if Symbol.Map.mem symbol psi_map then
        Symbol.Map.find symbol psi_map
      else
        mk_const ark symbol
    in
    mk_and ark [substitute_const ark phi_subst phi;
                substitute_const ark psi_subst psi]

  let closure ?(use_ocrs=false) split_iter =
    let ark = ark split_iter in
    let symbols = tr_symbols split_iter in
    let base_closure =
      if use_ocrs then
        closure_ocrs
      else
        closure
    in
    ExprMap.enum split_iter
    /@ (fun (predicate, (left, right)) ->
        let not_predicate = mk_not ark predicate in
        (sequence ark symbols
           (base_closure ~guard:(Some predicate) left)
           (base_closure ~guard:(Some not_predicate) right)))
    |> BatList.of_enum
    |> mk_and ark

  let join split_iter split_iter' =
    let f _ a b = match a,b with
      | Some (a_left, a_right), Some (b_left, b_right) ->
        Some (join a_left b_left, join a_right b_right)
      | _, _ -> None
    in
    let split_join = ExprMap.merge f split_iter split_iter' in
    if ExprMap.is_empty split_join then
      lift_split (join (lower_split split_iter) (lower_split split_iter))
    else
      split_join

  let widen split_iter split_iter' =
    let f _ a b = match a,b with
      | Some (a_left, a_right), Some (b_left, b_right) ->
        Some (widen a_left b_left, widen a_right b_right)
      | _, _ -> None
    in
    let split_widen = ExprMap.merge f split_iter split_iter' in
    if ExprMap.is_empty split_widen then
      lift_split (widen (lower_split split_iter) (lower_split split_iter))
    else
      split_widen

  let equal split_iter split_iter' =
    BatEnum.for_all
      (fun ((p,(l,r)), (p',(l',r'))) ->
         Formula.equal p p'
         && equal l l'
         && equal r r')
      (BatEnum.combine
         (ExprMap.enum split_iter,
          ExprMap.enum split_iter'))
end
