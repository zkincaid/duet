open Syntax
open BatPervasives

include Log.Make(struct let name = "ark.iteration" end)

module V = Linear.QQVector
module QQMatrix = Linear.QQMatrix

module IntSet = ArkUtil.Int.Set
module IntMap = ArkUtil.Int.Map
module DArray = BatDynArray

module QQUvp = Polynomial.QQUvp
module QQMvp = Polynomial.Mvp
module Monomial = Polynomial.Monomial

module CS = CoordinateSystem

module type PreDomain = sig
  type 'a t
  val pp : Format.formatter -> 'a t -> unit
  val show : 'a t -> string
  val closure : 'a t -> 'a formula
  val join : 'a t -> 'a t -> 'a t
  val widen : 'a t -> 'a t -> 'a t
  val equal : 'a t -> 'a t -> bool
  val tr_symbols : 'a t -> (symbol * symbol) list
end

module type Domain = sig
  include PreDomain
  val abstract_iter : ?exists:(symbol -> bool) ->
    'a context ->
    'a formula ->
    (symbol * symbol) list ->
    'a t
end

module type DomainPlus = sig
  include Domain
  val closure_plus : 'a t -> 'a formula
end

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

let reflexive_closure ark tr_symbols formula =
  let identity =
    List.map (fun (sym, sym') ->
        mk_eq ark (mk_const ark sym) (mk_const ark sym'))
      tr_symbols
    |> mk_and ark
  in
  mk_or ark [identity; formula]

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
let post_map tr_symbols =
  List.fold_left
    (fun map (sym, sym') -> Symbol.Map.add sym sym' map)
    Symbol.Map.empty
    tr_symbols

module WedgeVector = struct
  (*    x'    <=       (3 * x) +  y + 1
        --    --        -         -----
        exp_lhs exp_op exp_coeff    exp_add *)
  type 'a exponential =
    { exp_lhs : 'a term;
      exp_op : [ `Leq | `Eq ];
      exp_coeff : QQ.t;
      exp_rhs : 'a term;
      exp_add : 'a term }

  type 'a t =
    { ark : 'a context;
      symbols : (symbol * symbol) list;
      precondition : 'a Wedge.t;
      postcondition : 'a Wedge.t;
      stratified : (symbol * symbol * 'a term) list;
      exponential : ('a exponential) list }

  let pp formatter iter =
    let ark = iter.ark in
    Format.fprintf formatter
      "{@[<v 0>pre symbols:@;  @[<v 0>%a@]@;post symbols:@;  @[<v 0>%a@]@;"
      (ArkUtil.pp_print_enum (pp_symbol ark)) (BatList.enum iter.symbols /@ fst)
      (ArkUtil.pp_print_enum (pp_symbol ark)) (BatList.enum iter.symbols /@ snd);
    Format.fprintf formatter "pre:@;  @[<v 0>%a@]@;post:@;  @[<v 0>%a@]@;"
      Wedge.pp iter.precondition
      Wedge.pp iter.postcondition;
    Format.fprintf formatter
      "recurrences:@;  @[<v 0>%a@;%a@]@]}"
      (ArkUtil.pp_print_enum_nobox
         ~pp_sep:(fun formatter () -> Format.pp_print_break formatter 0 0)
         (fun formatter (sym', sym, incr) ->
            Format.fprintf formatter "%a = %a + %a"
              (pp_symbol ark) sym'
              (pp_symbol ark) sym
              (Term.pp ark) incr))
      (BatList.enum iter.stratified)
      (ArkUtil.pp_print_enum_nobox
         ~pp_sep:(fun formatter () -> Format.pp_print_break formatter 0 0)
         (fun formatter { exp_lhs; exp_op; exp_coeff; exp_rhs; exp_add } ->
            Format.fprintf formatter "(%a) %s %a * (%a) + %a"
              (Term.pp ark) exp_lhs
              (match exp_op with
               | `Eq -> "="
               | `Leq -> "<=")
              QQ.pp exp_coeff
              (Term.pp ark) exp_rhs
              (Term.pp ark) exp_add))
      (BatList.enum iter.exponential)

  let show x = ArkUtil.mk_show pp x

  let exponential_rec ark wedge non_induction post_symbols base =
    (* map from non-induction pre-state vars to their post-state
       counterparts *)
    let post_map = post_map non_induction in
    let postify =
      let subst sym =
        if Symbol.Map.mem sym post_map then
          mk_const ark (Symbol.Map.find sym post_map)
        else
          mk_const ark sym
      in
      substitute_const ark subst
    in
    (* Replace each non-induction pre-state variable v with the difference
       (v'-v)/base and project out post-state variables.  Pre-state induction
       variables ("delta variables") now represent the difference (v'-base*v) *)
    let diff_wedge =
      let delta_subst sym =
        if Symbol.Map.mem sym post_map then
          (* non-induction var *)
          mk_mul ark [mk_real ark (QQ.inverse base);
                      mk_add ark [mk_const ark (Symbol.Map.find sym post_map);
                                  mk_neg ark (mk_const ark sym)]]
        else
          mk_const ark sym
      in
      let rewrite = substitute_const ark delta_subst in
      (* don't allow delta vars as subterms *)
      let subterm sym = not (Symbol.Map.mem sym post_map) in
      Wedge.to_atoms wedge
      |> List.map rewrite
      |> Wedge.of_atoms ark
      |> Wedge.exists ~subterm (not % flip Symbol.Set.mem post_symbols)
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
      | `App (func, args) ->
        let is_delta sym = Symbol.Map.mem sym post_map in
        if List.exists (Symbol.Set.exists is_delta % symbols) args then
          None
        else
          Some (zero_term, mk_app ark func args)
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
      | `Ite (_, _, _) | `Var (_, _) -> None
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
               Some { exp_lhs = postify lhs;
                      exp_coeff = base;
                      exp_op = op;
                      exp_rhs = lhs;
                      exp_add = mk_neg ark rhs })
      | `Literal (_, _) -> None
    in
    BatList.filter_map recur (Wedge.to_atoms diff_wedge)

  let abstract_iter_wedge ark wedge tr_symbols =
    let pre_symbols = pre_symbols tr_symbols in
    let post_symbols = post_symbols tr_symbols in
    let is_symbolic_constant x =
      not (Symbol.Set.mem x pre_symbols || Symbol.Set.mem x post_symbols)
    in
    let precondition =
      Wedge.exists (not % flip Symbol.Set.mem post_symbols) wedge
    in
    let postcondition =
      Wedge.exists (not % flip Symbol.Set.mem pre_symbols) wedge
    in
    let (stratified, non_induction) =
      let equalities = Wedge.farkas_equalities wedge in
      (* Matrix consisting of one row for each dimension of the wedge that is
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
      let (candidates, non_induction) =
        List.partition (fun (s,s') ->
            Symbol.Map.mem s row_of_symbol && Symbol.Map.mem s' row_of_symbol)
          tr_symbols
      in
      let (induction, non_induction') = go [] candidates [] matrix in
      (induction, non_induction@non_induction')
    in
    let exponential =
      exponential_rec ark wedge non_induction post_symbols (QQ.of_int 1)
      @(exponential_rec ark wedge non_induction post_symbols (QQ.of_int 2))
      @(exponential_rec ark wedge non_induction post_symbols (QQ.of_frac 1 2))
    in
    { ark;
      symbols = tr_symbols;
      precondition;
      postcondition;
      stratified;
      exponential }

  let abstract_iter ?(exists=fun x -> true) ark phi symbols =
    let post_symbols =
      List.fold_left (fun set (_,s') ->
          Symbol.Set.add s' set)
        Symbol.Set.empty
        symbols
    in
    let subterm x = not (Symbol.Set.mem x post_symbols) in
    let wedge =
      Wedge.abstract ~exists ark phi
      |> Wedge.exists ~subterm (fun _ -> true)
    in
    abstract_iter_wedge ark wedge symbols

  let closure_plus (iter : 'a t) : 'a formula =
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
      BatList.filter_map (fun { exp_lhs; exp_op; exp_coeff; exp_rhs; exp_add } ->
          if QQ.equal exp_coeff QQ.one then
            match close_sum induction_vars exp_add with
            | None -> None
            | Some cf ->
              let rhs =
                mk_add iter.ark [exp_rhs; Cf.term_of iter.ark cf loop_counter]
              in
              match exp_op with
              | `Leq -> Some (mk_leq iter.ark exp_lhs rhs)
              | `Eq -> Some (mk_eq iter.ark exp_lhs rhs)
          else
            None)
        iter.exponential
      |> mk_and iter.ark
    in
    mk_and iter.ark [
      Wedge.to_formula iter.precondition;
      mk_leq iter.ark (mk_real iter.ark QQ.one) loop_counter;
      stratified;
      inequations;
      Wedge.to_formula iter.postcondition
    ]

  let closure iter =
    reflexive_closure iter.ark iter.symbols (closure_plus iter)

  let wedge_of_iter iter =
    let eq_constraints =
      iter.stratified |> List.map (fun (post, pre, incr) ->
          mk_eq iter.ark
            (mk_const iter.ark post)
            (mk_add iter.ark [mk_const iter.ark pre; incr]))
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
          | `Leq -> mk_leq iter.ark r.exp_lhs rhs)
    in
    let postcondition = Wedge.to_atoms iter.postcondition in
    let precondition = Wedge.to_atoms iter.precondition in
    Wedge.of_atoms
      iter.ark
      (eq_constraints@exponential_constraints@postcondition@precondition)

  let equal iter iter' =
    Wedge.equal (wedge_of_iter iter) (wedge_of_iter iter')

  let widen iter iter' =
    let body = Wedge.widen (wedge_of_iter iter) (wedge_of_iter iter') in
    assert(iter.symbols = iter'.symbols);
    abstract_iter_wedge iter.ark body iter.symbols

  let join iter iter' =
    let body =
      Wedge.join (wedge_of_iter iter) (wedge_of_iter iter')
    in
    assert(iter.symbols = iter'.symbols);
    abstract_iter_wedge iter.ark body iter.symbols

  let star ?(exists=fun x -> true) ark phi symbols =
    closure (abstract_iter ~exists ark phi symbols)

  let bottom ark symbols =
    { ark = ark;
      symbols = symbols;
      precondition = Wedge.bottom ark;
      postcondition = Wedge.bottom ark;
      stratified = [];
      exponential = [] }

  let tr_symbols iter = iter.symbols
end

module WedgeVectorOCRS = struct
  include WedgeVector

  exception No_translation
  let closure_plus iter =
    let open Ocrs in
    let open Type_def in

    Wedge.ensure_nonlinear_symbols iter.ark;
    let pow = get_named_symbol iter.ark "pow" in
    let log = get_named_symbol iter.ark "log" in

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
      let rec alg = function
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
        | `App (func, [x; y]) when func = pow ->
          begin match refine iter.ark x, refine iter.ark y with
            | `Term x, `Term y ->
              Pow (Term.eval iter.ark alg x,
                   Term.eval iter.ark alg y)
            | _ -> assert false
          end
        | `App (func, [x; y]) when func = log ->
          begin match destruct iter.ark x, refine iter.ark y with
            | `Real k, `Term y ->
              Log (Mpqf.to_mpq k, Term.eval iter.ark alg y)
            | _ -> assert false
          end
        | `App (sym, _) -> assert false (* to do *)
        | `Real k -> Rational (Mpqf.to_mpq k)
        | `Add xs -> Sum xs
        | `Mul xs -> Product xs
        | `Binop (`Div, x, y) -> Divide (x, y)
        | `Unop (`Neg, x) -> Minus (Rational (Mpq.of_int 0), x)
        | `Binop (`Mod, x, y) -> Mod (x, y)
        | `Unop (`Floor, Divide (x, Rational y)) -> IDivide (x, y)
        | `Unop (`Floor, _) -> raise No_translation
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
      | Pow (Rational k, y) ->
        let k = Mpqf.of_mpq k in
        let (base, exp) =
          if QQ.lt QQ.zero k && QQ.lt k QQ.one then
            (mk_real iter.ark (QQ.inverse k),
             mk_neg iter.ark (term_of_expr y))
          else
            (mk_real iter.ark k,
             term_of_expr y)
        in
        mk_app iter.ark pow [base; exp]
      | Pow (x, y) ->
        let base = term_of_expr x in
        let exp = term_of_expr y in
        mk_app iter.ark pow [base; exp]
      | Log (base, x) ->
        let x = term_of_expr x in
        mk_app iter.ark log [mk_real iter.ark (Mpqf.of_mpq base); x]
      | IDivide (x, y) ->
        mk_idiv iter.ark (term_of_expr x) (mk_real iter.ark (Mpqf.of_mpq y))
      | Mod (x, y) ->
        mk_mod iter.ark (term_of_expr x) (term_of_expr y)
      | Iif (func, arg) ->
        assert (arg = "k");
        let sym =
          if not (is_registered_name iter.ark func) then
            register_named_symbol iter.ark func (`TyFun ([`TyReal], `TyReal));
          get_named_symbol iter.ark func
        in
        mk_app iter.ark sym [loop_counter]
      | Binomial (_, _) | Factorial _ | Sin _ | Cos _ | Arctan _ | Pi ->
        assert false
    in

    let recurrences =
      let filter_translate f xs =
        xs |> BatList.filter_map (fun x ->
            try Some (f x)
            with No_translation -> None)
      in
      let stratified =
        filter_translate (fun (post, pre, term) ->
            (Output_variable (string_of_symbol pre, ss_pre),
             Equals (Output_variable (string_of_symbol pre, ss_post),
                     Plus (Output_variable (string_of_symbol pre, ss_pre),
                           expr_of_term term))))
          iter.stratified
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
            in
            (expr_of_term exp_rhs, ineq))
          iter.exponential
      in
      stratified@exponential
    in
    let closed =
      let to_formula = function
        | Equals (x, y) -> mk_eq iter.ark (term_of_expr x) (term_of_expr y)
        | LessEq (x, y) -> mk_leq iter.ark (term_of_expr x) (term_of_expr y)
        | Less (x, y) -> mk_lt iter.ark (term_of_expr x) (term_of_expr y)
        | GreaterEq (x, y) -> mk_leq iter.ark (term_of_expr y) (term_of_expr x)
        | Greater (x, y) -> mk_lt iter.ark (term_of_expr y) (term_of_expr x)
      in
      Log.time "OCRS"
        (List.map to_formula) (Ocrs.solve_rec_list_pair recurrences)
    in
    mk_and iter.ark ([
        Wedge.to_formula iter.precondition;
        mk_leq iter.ark (mk_real iter.ark QQ.one) loop_counter;
        Wedge.to_formula iter.postcondition
      ]@closed)

  let closure iter =
    reflexive_closure iter.ark iter.symbols (closure_plus iter)
end

module WedgeMatrix = struct
  type matrix_rec =
    { rec_transform : QQ.t array array;
      rec_add : QQMvp.t array }

  let rec_empty =
    { rec_transform = Array.make 0 (Array.make 0 QQ.zero);
      rec_add = Array.make 0 QQMvp.zero }

  (* Iteration domain element.  Recurrence equations have the form
     A_1 * x' = B_1 * A_1 * x + c_1
     ...
     A_n * x' = B_n * A_n * x + c_n

     where each A_i/B_i is a rational matrix and each c_i is a vector of
     polynomial over dimensions corresponding to constant terms and the rows
     of A_1 ... A_{i-1}.

     The list of B_i/c_i's is stored in rec_eq.  The list of A_is is stored
     implicitly in term_of_id, which associates integer identifiers with
     linear term (so term_of_id.(nb_constants) corresponds to the first row of
     A_1, term_of_id.(nb_constants+size(A_1)) corresponds to the first row of
     A_2, ...).  Similarly for inequations in rec_leq. *)
  type 'a t =
    { ark : 'a context;
      symbols : (symbol * symbol) list;
      precondition : 'a Wedge.t;
      postcondition : 'a Wedge.t;
      term_of_id : ('a term) array;
      nb_constants : int;
      rec_eq : matrix_rec list;
      rec_leq : matrix_rec }

  let pp formatter iter =
    let ark = iter.ark in
    let post_map = post_map iter.symbols in
    let postify =
      let subst sym =
        if Symbol.Map.mem sym post_map then
          mk_const ark (Symbol.Map.find sym post_map)
        else
          mk_const ark sym
      in
      substitute_const ark subst
    in
    let pp_id formatter id =
      Term.pp ark formatter iter.term_of_id.(id)
    in
    let pp_rec cmp offset formatter recurrence =
      recurrence.rec_transform |> Array.iteri (fun i row ->
          let nonzero = ref false in
          Format.fprintf formatter "(%a) %s @[<hov 1>"
            (Term.pp ark) (postify iter.term_of_id.(offset + i))
            cmp;
          row |> Array.iteri (fun j coeff ->
              if not (QQ.equal coeff QQ.zero) then begin
                if !nonzero then
                  Format.fprintf formatter "@ + "
                else
                  nonzero := true;
                Format.fprintf formatter "(%a)*(%a)"
                  QQ.pp coeff
                  (Term.pp ark) (iter.term_of_id.(offset + j))
              end
            );
          if !nonzero then
            Format.fprintf formatter "@ + ";
          Format.fprintf formatter "%a@]@;"
            (QQMvp.pp pp_id) recurrence.rec_add.(i))
    in
    Format.fprintf formatter
      "{@[<v 0>pre symbols:@;  @[<v 0>%a@]@;post symbols:@;  @[<v 0>%a@]@;"
      (ArkUtil.pp_print_enum (pp_symbol ark)) (BatList.enum iter.symbols /@ fst)
      (ArkUtil.pp_print_enum (pp_symbol ark)) (BatList.enum iter.symbols /@ snd);
    Format.fprintf formatter "pre:@;  @[<v 0>%a@]@;post:@;  @[<v 0>%a@]@;recurrences:@;  @[<v 0>"
      Wedge.pp iter.precondition
      Wedge.pp iter.postcondition;
    let offset =
      List.fold_left (fun offset recurrence ->
          pp_rec "=" offset formatter recurrence;
          (Array.length recurrence.rec_transform + offset))
        iter.nb_constants
        iter.rec_eq
    in
    pp_rec "<=" offset formatter iter.rec_leq;
    Format.fprintf formatter "@]@]}"

  let show x = ArkUtil.mk_show pp x

  (* Are most coefficients of a vector negative? *)
  let is_vector_negative vec =
    let sign =
      BatEnum.fold (fun sign (coeff,_) ->
          if QQ.lt coeff QQ.zero then
            sign - 1
          else
            sign + 1)
        0
        (V.enum vec)
    in
    sign < 0

  (* Given matrices A and B, find a matrix C whose rows constitute a basis for
     the vector space { v : exists u. uA = vB } *)
  let max_rowspace_projection a b =
    (* Create a system u*A - v*B = 0.  u's occupy even columns and v's occupy
       odd. *)
    let mat_a =
      BatEnum.fold
        (fun mat (i, j, k) -> QQMatrix.add_entry j (2*i) k mat)
        QQMatrix.zero
        (QQMatrix.entries a)
    in
    let mat =
      ref (BatEnum.fold
             (fun mat (i, j, k) -> QQMatrix.add_entry j (2*i + 1) (QQ.negate k) mat)
             mat_a
             (QQMatrix.entries b))
    in
    let c = ref QQMatrix.zero in
    let c_rows = ref 0 in
    let mat_rows =
      ref (BatEnum.fold (fun m (i, _) -> max m i) 0 (QQMatrix.rowsi (!mat)) + 1)
    in

    (* Loop through the columns col of A/B, trying to find a vector u and v such
       that uA = vB and v has 1 in col's entry.  If yes, add v to C, and add a
       constraint to mat that (in all future rows of C), col's entry is 0.
       This ensures that the rows of C are linearly independent. *)
    (* to do: repeatedly solving super systems of the same system of equations
         -- can be made more efficient *)
    (QQMatrix.rowsi b)
    |> (BatEnum.iter (fun (r, _) ->
        let col = 2*r + 1 in
        let mat' =
          QQMatrix.add_row
            (!mat_rows)
            (V.of_term QQ.one col)
            (!mat)
        in
        match Linear.solve mat' (V.of_term QQ.one (!mat_rows)) with
        | Some solution ->
          let c_row =
            BatEnum.fold (fun c_row (entry, i) ->
                if i mod 2 = 1 then
                  V.add_term entry (i/2) c_row
                else
                  c_row)
              V.zero
              (V.enum solution)
          in
          assert (not (V.equal c_row V.zero));
          c := QQMatrix.add_row (!c_rows) c_row (!c);
          mat := mat';
          incr c_rows; incr mat_rows
        | None -> ()));
    !c

  (* Matrix-polynomial vector multiplication.  Assumes that the columns of m
     are a subset of {0,...,|polyvec|-1}. *)
  let matrix_polyvec_mul m polyvec =
    Array.init (QQMatrix.nb_rows m) (fun i ->
        BatEnum.fold (fun p (coeff, j) ->
            QQMvp.add p (QQMvp.scalar_mul coeff polyvec.(j)))
          QQMvp.zero
          (V.enum (QQMatrix.row i m)))

  exception IllFormedRecurrence

  (* Given a wedge w, compute A,B,C such that w |= Ax' = BAx + Cy, and such that
     the row space of A is maximal. *)
  let extract_affine_transformation ark wedge tr_symbols rec_terms rec_ideal =
    let cs = Wedge.coordinate_system wedge in

    (* pre_dims is a set of dimensions corresponding to pre-state
       dimensions. pre_map is a mapping from dimensions that correspond to
       post-state dimensions to their pre-state counterparts *)
    let (pre_map, pre_dims) =
      List.fold_left (fun (pre_map, pre_dims) (s,s') ->
          let id_of_sym sym =
            try
              CS.cs_term_id cs (`App (sym, []))
            with Not_found ->
              assert false
          in
          let pre = id_of_sym s in
          let post = id_of_sym s' in
          (IntMap.add post pre pre_map, IntSet.add pre pre_dims))
        (IntMap.empty, IntSet.empty)
        tr_symbols
    in

    let cs_dim = CS.dim cs in
    let additive_dim x = x >= cs_dim in
    let rec_term_rewrite =
      let ideal = ref rec_ideal in
      let elim_order =
        Monomial.block [not % additive_dim] Monomial.degrevlex
      in
      rec_terms |> DArray.iteri (fun i t ->
          let vec = CS.vec_of_term cs t in
          let p =
            QQMvp.add_term
              (QQ.of_int (-1))
              (Monomial.singleton (i + cs_dim) 1)
              (QQMvp.of_vec ~const:(CS.const_id) vec)
          in
          ideal := p::(!ideal));
      Polynomial.Rewrite.mk_rewrite elim_order (!ideal)
    in
    let basis =
      BatList.filter_map
        (fun x ->
           let x' = Polynomial.Rewrite.reduce rec_term_rewrite x in
           if QQMvp.equal x' QQMvp.zero then
             None
           else
             Some x')
        (Wedge.vanishing_ideal wedge)
    in

    (* Write the equations in wedge as Ax' = Bx + c, where c is vector of
       polynomials. *)
    let (mA, mB, pvc, _) =
      logf ~attributes:[`Bold] "Vanishing ideal:";
      List.fold_left (fun (mA,mB,pvc,i) p ->
          try
            logf "  @[%a@]" (QQMvp.pp (fun formatter i ->
                if i < cs_dim then
                  Format.fprintf formatter "w[%a]" (Term.pp ark) (CS.term_of_coordinate cs i)
                else
                  Format.fprintf formatter "v[%a]" (Term.pp ark) (DArray.get rec_terms (i - cs_dim)))) p;
            let (vecA, vecB, pc) =
              BatEnum.fold (fun (vecA, vecB, pc) (coeff, monomial) ->
                  match BatList.of_enum (Monomial.enum monomial) with
                  | [(dim, 1)] when IntMap.mem dim pre_map ->
                    (V.add_term (QQ.negate coeff) (IntMap.find dim pre_map) vecA,
                     vecB,
                     pc)
                  | [(dim, 1)] when IntSet.mem dim pre_dims ->
                    (vecA, V.add_term coeff dim vecB, pc)
                  | monomial_list ->
                    if List.for_all (additive_dim % fst) monomial_list then
                      (vecA, vecB, QQMvp.add_term coeff monomial pc)
                    else
                      raise IllFormedRecurrence)
                (V.zero, V.zero, QQMvp.zero)
                (QQMvp.enum p)        
            in
            let (vecA, vecB, pc) =
              if is_vector_negative vecA then
                (V.negate vecA, V.negate vecB, QQMvp.negate pc)
              else
                (vecA, vecB, pc)
            in
            let pc =
              QQMvp.substitute (fun i ->
                  QQMvp.add_term
                    QQ.one
                    (Monomial.singleton (i - cs_dim) 1)
                    QQMvp.zero)
                pc
            in
            if V.is_zero vecA then
              (mA,mB,pvc,i)
            else
              (QQMatrix.add_row i vecA mA,
               QQMatrix.add_row i vecB mB,
               pc::pvc,
               i+1)
          with IllFormedRecurrence -> (mA, mB, pvc, i))
        (QQMatrix.zero, QQMatrix.zero, [], 0)
        basis
    in
    let pvc = Array.of_list (List.rev pvc) in

    (* We have a system of the form Ax' = Bx + c, and we need one of the form
       Ax' = B'Ax + c.  If we can factor B = B'A, we're done.  Otherwise, we
       compute an m-by-n matrix D with m < n, and continue iterating with the
       system DAx' = DBx + Dc.  The matrix D projects B onto the intersection of
       the row spaces of A and B.  *)
    let rec fix mA mB pvc =
      let mD = max_rowspace_projection mA mB in
      if QQMatrix.nb_rows mB = QQMatrix.nb_rows mD then
        match Linear.divide_right mB mA with
        | Some mB' ->
          assert (QQMatrix.equal (QQMatrix.mul mB' mA) mB);
          (mA, mB', pvc) (* mB = mB'*A *)
        | None ->
          (* D's rows are linearly independent -- if it has as many rows as B,
             then the rowspace of B is contained inside the rowspace of A, and
             B/A is defined. *)
          assert false
      else
        fix (QQMatrix.mul mD mA) (QQMatrix.mul mD mB) (matrix_polyvec_mul mD pvc)
    in
    let (mA,mB,pvc) =
      fix mA mB pvc
    in
    logf ~attributes:[`Blue] "Affine transformation:";
    logf " A: @[%a@]" QQMatrix.pp mA;
    logf " B: @[%a@]" QQMatrix.pp mB;
    (mA,mB,pvc)

  let extract_leq ark wedge tr_symbols =
    let open Apron in
    let cs = Wedge.coordinate_system wedge in
    let man = Polka.manager_alloc_loose () in
    let coeff_of_qq = Coeff.s_of_mpqf in
    let qq_of_coeff = function
      | Coeff.Scalar (Scalar.Float k) -> QQ.of_float k
      | Coeff.Scalar (Scalar.Mpqf k)  -> k
      | Coeff.Scalar (Scalar.Mpfrf k) -> Mpfrf.to_mpqf k
      | Coeff.Interval _ -> assert false
    in
    let linexpr_of_vec vec =
      let mk (coeff, id) = (coeff_of_qq coeff, id) in
      let (const_coeff, rest) = V.pivot CS.const_id vec in
      Linexpr0.of_list None
        (BatList.of_enum (BatEnum.map mk (V.enum rest)))
        (Some (coeff_of_qq const_coeff))
    in
    let vec_of_linexpr linexpr =
      let vec = ref V.zero in
      linexpr |> Linexpr0.iter (fun coeff dim ->
          vec := V.add_term (qq_of_coeff coeff) dim (!vec));
      V.add_term (qq_of_coeff (Linexpr0.get_cst linexpr)) CS.const_id (!vec)
    in

    let tr_coord =
      try
        List.map (fun (s,s') ->
            (CS.cs_term_id cs (`App (s, [])),
             CS.cs_term_id cs (`App (s', []))))
          tr_symbols
        |> Array.of_list
      with Not_found -> assert false
    in

    let rec fix polyhedron =
      let open Lincons0 in
      (* Polyhedron is of the form Ax' <= Bx + Cy, or equivalently,
         [-A B C]*[x' x y] >= 0. constraints is an array consisting of the
         rows of [-A B C].  *)
      logf "Polyhedron: %a"
        (Abstract0.print
           ((ArkUtil.mk_show (Term.pp ark)) % CS.term_of_coordinate cs))
        polyhedron;
      let constraints = DArray.create () in
      Abstract0.to_lincons_array man polyhedron
      |> Array.iter (fun lincons ->
          let vec = vec_of_linexpr lincons.linexpr0 in
          DArray.add constraints vec;
          if lincons.typ = EQ then
            DArray.add constraints (V.negate vec));
      let nb_constraints = DArray.length constraints in

      (* vu_cone is the cone { [v u] : u >= 0, v >= 0 uA = vB } *)
      let vu_cone =
        let pos_constraints = (* u >= 0, v >= 0 *)
          Array.init (2 * nb_constraints) (fun i ->
              Lincons0.make
                (Linexpr0.of_list None [(coeff_of_qq QQ.one, i)] None)
                SUPEQ)
          |> Abstract0.of_lincons_array man 0 (2 * nb_constraints)
        in
        Array.init (Array.length tr_coord) (fun i ->
            let (pre, post) = tr_coord.(i) in
            let linexpr = Linexpr0.make None in
            for j = 0 to nb_constraints - 1 do
              let vec = DArray.get constraints j in
              Linexpr0.set_coeff linexpr j (coeff_of_qq (V.coeff pre vec));
              Linexpr0.set_coeff
                linexpr
                (j + nb_constraints)
                (coeff_of_qq (V.coeff post vec));
            done;
            Lincons0.make linexpr Lincons0.EQ)
        |> Abstract0.meet_lincons_array man pos_constraints
      in
      (* Project vu_cone onto the v dimensions and compute generators. *)
      let v_generators =
        Abstract0.remove_dimensions
          man
          vu_cone
          { Dim.dim =
              (Array.init nb_constraints (fun i -> nb_constraints + i));
            Dim.intdim = 0;
            Dim.realdim = nb_constraints }
        |> Abstract0.to_generator_array man
      in
      (* new_constraints is v_generators * [-A B C]*)
      let new_constraints =
        Array.fold_right (fun gen nc ->
            let open Generator0 in
            let vec = vec_of_linexpr gen.linexpr0 in
            let row =
              BatEnum.fold (fun new_row (coeff, dim) ->
                  assert (dim < nb_constraints);
                  V.scalar_mul coeff (DArray.get constraints dim)
                  |> V.add new_row)
                V.zero
                (V.enum vec)
              |> linexpr_of_vec
            in
            assert (QQ.equal QQ.zero (V.coeff CS.const_id vec));
            if gen.typ = RAY then
              (Lincons0.make row Lincons0.SUPEQ)::nc
            else if gen.typ = VERTEX then begin
              assert (V.equal V.zero vec); (* should be the origin *)
              nc
            end else
              assert false)
          v_generators
          []
        |> Array.of_list
      in
      let new_polyhedron =
        Abstract0.of_lincons_array man 0 (CS.dim cs) new_constraints
      in
      if Abstract0.is_eq man polyhedron new_polyhedron then
        if nb_constraints = 0 then
          (QQMatrix.zero,
           Array.make 0 (Array.make 0 QQ.zero),
           Array.make 0 QQMvp.zero)
        else
          let mA =
            BatEnum.fold (fun mA i ->
                let row =
                  BatEnum.fold (fun row j ->
                      let (pre, post) = tr_coord.(j) in
                      V.add_term
                        (QQ.negate (V.coeff post (DArray.get constraints i)))
                        pre
                        row)
                    V.zero
                    (0 -- (Array.length tr_coord - 1))
                in
                QQMatrix.add_row i row mA)
              QQMatrix.zero
              (0 -- (nb_constraints - 1))
          in

          (* Find a non-negative M such that B=M*A *)
          let m_entries = (* corresponds to one generic row of M *)
            Array.init nb_constraints (fun i -> mk_symbol ark `TyReal)
          in
          (* Each entry of M must be non-negative *)
          let pos_constraints =
            List.map (fun sym ->
                mk_leq ark (mk_real ark QQ.zero) (mk_const ark sym))
              (Array.to_list m_entries)
          in
          let m_times_a =
            (0 -- (Array.length tr_coord - 1))
            /@ (fun i ->
                let (pre, post) = tr_coord.(i) in
                (0 -- (nb_constraints - 1))
                /@ (fun j ->
                    mk_mul ark [mk_const ark m_entries.(j);
                                mk_real ark (QQMatrix.entry j pre mA)])
                |> BatList.of_enum
                |> mk_add ark)
            |> BatArray.of_enum
          in
          (* B[i,j] = M[i,1]*A[1,j] + ... + M[i,n]*A[n,j] *)
          let mB =
            Array.init nb_constraints (fun i ->
                let row_constraints =
                  (0 -- (Array.length tr_coord - 1))
                  /@ (fun j ->
                      let (pre, post) = tr_coord.(j) in
                      mk_eq ark
                        m_times_a.(j)
                        (mk_real ark (V.coeff pre (DArray.get constraints i))))
                  |> BatList.of_enum
                in
                let s = Smt.mk_solver ark in
                s#add pos_constraints;
                s#add row_constraints;
                let model =
                  (* First try for a simple recurrence, then fall back *)
                  s#push ();
                  (0 -- (Array.length m_entries - 1))
                  /@ (fun j ->
                      if i = j then
                        mk_true ark
                      else
                        mk_eq ark (mk_const ark m_entries.(j)) (mk_real ark QQ.zero))
                  |> BatList.of_enum
                  |> s#add;
                  match s#get_model () with
                  | `Sat model -> model
                  | _ ->
                    s#pop 1;
                    match s#get_model () with
                    | `Sat model -> model
                    | _ -> assert false
                in
                Array.init nb_constraints (fun i ->
                    model#eval_real (mk_const ark m_entries.(i))))
          in
          let pvc =
            Array.init nb_constraints (fun i ->
                QQMvp.scalar (V.coeff CS.const_id (DArray.get constraints i)))
          in
          (mA,mB,pvc)
      else
        fix (Abstract0.widening man polyhedron new_polyhedron)
    in
    (* TODO: reduce each halfspace *)
    let polyhedron =
      let constraints =
        BatList.filter_map
          (function
            | (`Eq, vec) ->
              Some (Lincons0.make (linexpr_of_vec vec) Lincons0.EQ)
            | (`Geq, vec) ->
              Some (Lincons0.make (linexpr_of_vec vec) Lincons0.SUPEQ))
          (Wedge.polyhedron wedge)
        |> Array.of_list
      in
      Abstract0.of_lincons_array
        man
        0
        (CS.dim cs)
        constraints
    in
    let tr_coord_set =
      Array.fold_left
        (fun set (d,d') -> IntSet.add d (IntSet.add d' set))
        IntSet.empty
        tr_coord
    in
    let forget =
      let non_tr_coord =
        BatEnum.fold (fun non_tr dim ->
            if IntSet.mem dim tr_coord_set then
              non_tr
            else
              dim::non_tr)
          []
          (0 -- (CS.dim cs - 1))
      in
      Array.of_list (List.rev non_tr_coord)
    in
    let polyhedron =
      Abstract0.forget_array
        man
        polyhedron
        forget
        false
    in
    fix polyhedron

  let abstract_iter_wedge ark wedge tr_symbols =
    logf "--------------- Abstracting wedge ---------------@\n%a)" Wedge.pp wedge;
    let cs = Wedge.coordinate_system wedge in
    let pre_symbols = pre_symbols tr_symbols in
    let post_symbols = post_symbols tr_symbols in
    let precondition =
      Wedge.exists (not % flip Symbol.Set.mem post_symbols) wedge
    in
    let postcondition =
      Wedge.exists (not % flip Symbol.Set.mem pre_symbols) wedge
    in
    let (rec_wedge, rec_sym) =
      let (non_recursive, rec_sym) =
        List.fold_left (fun (set, rec_sym) (s,s') ->
            if CS.admits cs (mk_const ark s) && CS.admits cs (mk_const ark s') then
              (set, (s,s')::rec_sym)
            else
              (Symbol.Set.add s (Symbol.Set.add s' set), rec_sym))
          (Symbol.Set.empty, [])
          tr_symbols
      in
      if Symbol.Set.is_empty non_recursive then
        (wedge, rec_sym)
      else
        (Wedge.exists (not % flip Symbol.Set.mem non_recursive) wedge, rec_sym)
    in
    let cs = Wedge.coordinate_system rec_wedge in
    let post_coord_map =
      (* map pre-state coordinates to their post-state counterparts *)
      List.fold_left
        (fun map (sym, sym') ->
           try
             let coord = CS.cs_term_id cs (`App (sym, [])) in
             let coord' = CS.cs_term_id cs (`App (sym', [])) in
             IntMap.add coord coord' map
           with Not_found -> map)
        IntMap.empty
        tr_symbols
    in

    let term_of_id = DArray.create () in

    (* Detect constant terms *)
    let is_symbolic_constant x =
      not (Symbol.Set.mem x pre_symbols || Symbol.Set.mem x post_symbols)
    in
    let constant_symbols = ref Symbol.Set.empty in
    for i = 0 to CS.dim cs - 1 do
      let term = CS.term_of_coordinate cs i in
      match Term.destruct ark term with
      | `App (sym, []) ->
        if is_symbolic_constant sym then begin
          constant_symbols := Symbol.Set.add sym (!constant_symbols);
          DArray.add term_of_id term
        end
      | _ ->
        if Symbol.Set.subset (symbols term) (!constant_symbols) then
          DArray.add term_of_id term
    done;
    let nb_constants = DArray.length term_of_id in

    (* Detect stratified recurrences *)
    let rec fix rec_ideal =
      let offset = DArray.length term_of_id in
      logf "New stratum (%d recurrence terms)" (DArray.length term_of_id);
      let (mA,mB,rec_add) =
        extract_affine_transformation ark rec_wedge rec_sym term_of_id rec_ideal
      in
      let size = Array.length rec_add in
      if size = 0 then
        []
      else
        let rec_transform =
          Array.init size (fun row ->
              Array.init size (fun col ->
                  QQMatrix.entry row col mB))
        in
        let rec_ideal' = ref rec_ideal in
        for i = 0 to size - 1 do
          DArray.add term_of_id (CS.term_of_vec cs (QQMatrix.row i mA))
        done;
        for i = 0 to size - 1 do
          let rec_eq =
            let lhs =
              QQMvp.of_vec ~const:CS.const_id (QQMatrix.row i mA)
              |> QQMvp.substitute (fun coord ->
                  assert (IntMap.mem coord post_coord_map);
                  QQMvp.of_dim (IntMap.find coord post_coord_map))
            in
            let add =
              QQMvp.substitute (fun i ->
                  (CS.polynomial_of_term cs (DArray.get term_of_id i)))
                rec_add.(i)
            in
            let rhs =
              BatEnum.fold (fun p (coeff, i) ->
                  if i = CS.const_id then
                    QQMvp.add (QQMvp.scalar coeff) p
                  else
                    QQMvp.add p
                      (QQMvp.scalar_mul coeff
                         (CS.polynomial_of_term cs
                            (DArray.get term_of_id (offset + i)))))
                QQMvp.zero
                (V.enum (QQMatrix.row i mB))
              |> QQMvp.add add
            in
            QQMvp.add lhs (QQMvp.negate rhs)
          in
          rec_ideal' := rec_eq::(!rec_ideal')
        done;
        { rec_transform; rec_add }::(fix (!rec_ideal'))
    in
    let rec_eq = fix [] in
    let rec_leq =
      let (mA, rec_transform, rec_add) = extract_leq ark rec_wedge rec_sym in
      let size = Array.length rec_add in
      for i = 0 to size - 1 do
        DArray.add term_of_id (CS.term_of_vec cs (QQMatrix.row i mA))
      done;
      { rec_transform; rec_add }
    in
    let result =
    { ark;
      symbols = tr_symbols;
      precondition;
      postcondition;
      nb_constants;
      term_of_id = DArray.to_array term_of_id;
      rec_eq = rec_eq;
      rec_leq = rec_leq }
    in
    logf "=============== Wedge/Matrix recurrence ===============@\n%a)" pp result;
    result

  let abstract_iter ?(exists=fun x -> true) ark phi symbols =
    let post_symbols =
      List.fold_left (fun set (_,s') ->
          Symbol.Set.add s' set)
        Symbol.Set.empty
        symbols
    in
    let subterm x = not (Symbol.Set.mem x post_symbols) in
    let wedge =
      Wedge.abstract ~exists ~subterm ark phi
    in
    abstract_iter_wedge ark wedge symbols

  let closure_plus iter =
    let open Ocrs in
    let open Type_def in

    Wedge.ensure_nonlinear_symbols iter.ark;
    let pow = get_named_symbol iter.ark "pow" in
    let log = get_named_symbol iter.ark "log" in

    let loop_counter_sym = mk_symbol iter.ark ~name:"K" `TyInt in
    let loop_counter = mk_const iter.ark loop_counter_sym in

    let post_map = (* map pre-state vars to post-state vars *)
      post_map iter.symbols
    in

    let postify =
      let subst sym =
        if Symbol.Map.mem sym post_map then
          mk_const iter.ark (Symbol.Map.find sym post_map)
        else
          mk_const iter.ark sym
      in
      substitute_const iter.ark subst
    in

    (* pre/post subscripts *)
    let ss_pre = SSVar "k" in
    let ss_post = SAdd ("k", 1) in

    (* Map identifiers to their closed forms, so that they can be used in the
       additive term of recurrences at higher strata *)
    let cf =
      Array.make (Array.length iter.term_of_id) (Rational (Mpqf.to_mpq QQ.zero))
    in
    for i = 0 to iter.nb_constants - 1 do
      cf.(i) <- Symbolic_Constant (string_of_int i)
    done;
    let rec term_of_expr = function
      | Plus (x, y) -> mk_add iter.ark [term_of_expr x; term_of_expr y]
      | Minus (x, y) -> mk_sub iter.ark (term_of_expr x) (term_of_expr y)
      | Times (x, y) -> mk_mul iter.ark [term_of_expr x; term_of_expr y]
      | Divide (x, y) -> mk_div iter.ark (term_of_expr x) (term_of_expr y)
      | Product xs -> mk_mul iter.ark (List.map term_of_expr xs)
      | Sum xs -> mk_add iter.ark (List.map term_of_expr xs)
      | Symbolic_Constant name ->
        iter.term_of_id.(int_of_string name)
      | Base_case (name, index) ->
        assert (index = 0);
        iter.term_of_id.(int_of_string name)
      | Input_variable name ->
        assert (name = "k");
        loop_counter
      | Output_variable (name, subscript) ->
        assert (subscript = ss_pre);
        let id = int_of_string name in
        postify (iter.term_of_id.(id))
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
      | Pow (Rational k, y) ->
        let k = Mpqf.of_mpq k in
        let (base, exp) =
          if QQ.lt QQ.zero k && QQ.lt k QQ.one then
            (mk_real iter.ark (QQ.inverse k),
             mk_neg iter.ark (term_of_expr y))
          else
            (mk_real iter.ark k,
             term_of_expr y)
        in
        mk_app iter.ark pow [base; exp]
      | Pow (x, y) ->
        let base = term_of_expr x in
        let exp = term_of_expr y in
        mk_app iter.ark pow [base; exp]
      | Log (base, x) ->
        let x = term_of_expr x in
        mk_app iter.ark log [mk_real iter.ark (Mpqf.of_mpq base); x]
      | IDivide (x, y) ->
        mk_idiv iter.ark (term_of_expr x) (mk_real iter.ark (Mpqf.of_mpq y))
      | Mod (x, y) ->
        mk_mod iter.ark (term_of_expr x) (term_of_expr y)
      | Iif (func, arg) ->
        assert (arg = "k");
        let sym =
          if not (is_registered_name iter.ark func) then
            register_named_symbol iter.ark func (`TyFun ([`TyReal], `TyReal));
          get_named_symbol iter.ark func
        in
        mk_app iter.ark sym [loop_counter]
      | Binomial (_, _) | Factorial _ | Sin _ | Cos _ | Arctan _ | Pi ->
        assert false
    in
    let close_matrix_rec recurrence offset =
      let size = Array.length recurrence.rec_add in
      let dim_vec = Array.init size (fun i -> string_of_int (offset+i)) in
      let ocrs_transform =
        Array.map (Array.map Mpqf.to_mpq) recurrence.rec_transform
      in
      let ocrs_add =
        Array.init size (fun i ->
            let cf_monomial m =
              Monomial.enum m
              /@ (fun (id, pow) -> Pow (cf.(id), Rational (Mpq.of_int pow)))
              |> BatList.of_enum
            in
            QQMvp.enum recurrence.rec_add.(i)
            /@ (fun (coeff, m) ->
                Product (Rational (Mpqf.to_mpq coeff)::(cf_monomial m)))
            |> (fun x -> Sum (BatList.of_enum x)))
      in
      let recurrence_closed =
        let mat_rec =
          VEquals (Ovec (dim_vec, ss_post),
                   ocrs_transform,
                   Ovec (dim_vec, ss_pre),
                   ocrs_add)
        in
        logf "Matrix recurrence:@\n%s" (Mat_helpers.matrix_rec_to_string mat_rec);
        Log.time "OCRS" (Ocrs.solve_mat_recurrence mat_rec) false
      in
      recurrence_closed
    in
    let rec close offset closed = function
      | [] -> (mk_and iter.ark closed, offset)
      | (recurrence::rest) ->
        let size = Array.length recurrence.rec_add in
        let recurrence_closed = close_matrix_rec recurrence offset in
        let to_formula = function
          | Equals (x, y) -> mk_eq iter.ark (term_of_expr y) (term_of_expr x)
          | _ -> assert false
        in
        recurrence_closed |> List.iteri (fun i ineq ->
            match ineq with
            | Equals (x, y) | LessEq (x, y) | Less (x, y)
            | GreaterEq (x, y) | Greater (x, y) ->
              cf.(offset + i) <- y);
        let recurrence_closed_formula = List.map to_formula recurrence_closed in
        close (offset + size) (recurrence_closed_formula@closed) rest
    in
    let (closed, offset) = close iter.nb_constants [] iter.rec_eq in
    let closed_leq =
      let to_formula = function
        | Equals (x, y) -> mk_leq iter.ark (term_of_expr x) (term_of_expr y)
        | _ -> assert false
      in
      if Array.length iter.rec_leq.rec_add > 0 then
        let recurrence_closed = close_matrix_rec iter.rec_leq offset in
        List.map to_formula recurrence_closed
        |> mk_and iter.ark
      else
        mk_true iter.ark
    in
    mk_and iter.ark [
        Wedge.to_formula iter.precondition;
        mk_leq iter.ark (mk_real iter.ark QQ.one) loop_counter;
        Wedge.to_formula iter.postcondition;
        closed;
        closed_leq
    ]

  let closure iter =
    reflexive_closure iter.ark iter.symbols (closure_plus iter)

  let wedge_of_iter iter =
    let post_map =
      List.fold_left
        (fun map (sym, sym') -> Symbol.Map.add sym sym' map)
        Symbol.Map.empty
        iter.symbols
    in
    let postify =
      let subst sym =
        if Symbol.Map.mem sym post_map then
          mk_const iter.ark (Symbol.Map.find sym post_map)
        else
          mk_const iter.ark sym
      in
      substitute_const iter.ark subst
    in
    let rec_atoms mk_compare offset recurrence =
      recurrence.rec_transform |> Array.mapi (fun i row ->
          let term = iter.term_of_id.(offset + i) in
          let rhs_add =
            QQMvp.term_of
              iter.ark
              (fun j -> iter.term_of_id.(j))
              recurrence.rec_add.(i)
          in
          let rhs =
            BatArray.fold_lefti (fun rhs j coeff ->
                if QQ.equal coeff QQ.zero then
                  rhs
                else
                  let jterm =
                    mk_mul iter.ark [mk_real iter.ark coeff;
                                     iter.term_of_id.(offset + j)]
                  in
                  jterm::rhs)
              [rhs_add]
              row
            |> mk_add iter.ark
          in
          mk_compare (postify term) rhs)
      |> BatArray.to_list
    in
    let atoms =
      (Wedge.to_atoms iter.precondition)@(Wedge.to_atoms iter.postcondition)
    in
    let (offset, atoms) =
      BatList.fold_left (fun (offset, atoms) recurrence ->
          let size = Array.length recurrence.rec_add in
          (offset+size,
           (rec_atoms (mk_eq iter.ark) offset recurrence)@atoms))
        (iter.nb_constants, atoms)
        iter.rec_eq
    in
    let atoms =
      (rec_atoms (mk_leq iter.ark) offset iter.rec_leq)@atoms
    in
    Wedge.of_atoms iter.ark atoms

  let equal iter iter' =
    Wedge.equal (wedge_of_iter iter) (wedge_of_iter iter')

  let widen iter iter' =
    let body = Wedge.widen (wedge_of_iter iter) (wedge_of_iter iter') in
    assert(iter.symbols = iter'.symbols);
    abstract_iter_wedge iter.ark body iter.symbols

  let join iter iter' =
    let body =
      Wedge.join (wedge_of_iter iter) (wedge_of_iter iter')
    in
    assert(iter.symbols = iter'.symbols);
    abstract_iter_wedge iter.ark body iter.symbols

  let tr_symbols iter = iter.symbols
end

module Split (Iter : DomainPlus) = struct
  type 'a t =
    { ark : 'a context;
      split : ('a, typ_bool, 'a Iter.t * 'a Iter.t) ExprMap.t }

  let tr_symbols split_iter =
    match BatEnum.get (ExprMap.values split_iter.split) with
    | Some (iter, _) -> Iter.tr_symbols iter
    | None -> assert false

  let pp formatter split_iter =
    let pp_elt formatter (pred,(left,right)) =
      Format.fprintf formatter "[@[<v 0>%a@; %a@; %a@]]"
        (Formula.pp split_iter.ark) pred
        Iter.pp left
        Iter.pp right
    in
    Format.fprintf formatter "<Split @[<v 0>%a@]>"
      (ArkUtil.pp_print_enum pp_elt) (ExprMap.enum split_iter.split)

  let show x = ArkUtil.mk_show pp x

  (* Lower a split iter into an iter by picking an arbitary split and joining
     both sides. *)
  let lower_split split_iter =
    match BatEnum.get (ExprMap.values split_iter.split) with
    | Some (iter, iter') -> Iter.join iter iter'
    | None -> assert false

  let base_bottom ark symbols = Iter.abstract_iter ark (mk_false ark) symbols

  let lift_split ark iter =
    { ark = ark;
      split = (ExprMap.add
                 (mk_true ark)
                 (iter, base_bottom ark (Iter.tr_symbols iter))
                 ExprMap.empty) }

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
        ~up:(Nonlinear.uninterpret_rewriter ark)
        body
    in
    let solver = Smt.mk_solver ark in
    solver#add [uninterp_body];
    let sat_modulo_body psi =
      let psi =
        rewrite ark
          ~up:(Nonlinear.uninterpret_rewriter ark)
          psi
      in
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
            Iter.abstract_iter ~exists ark not_psi_body tr_symbols
          in
          let right_abstract =
            Iter.abstract_iter ~exists ark psi_body tr_symbols
          in
          ExprMap.add not_psi (left_abstract, right_abstract) split_iter
        else if sat_modulo_body (mk_and ark [not_psi; post_psi]) = `Unsat then
          (* {not phi} body {not phi} -> body* = ([phi]body)*([not phi]body)* *)
          let left_abstract =
            Iter.abstract_iter ~exists ark psi_body tr_symbols
          in
          let right_abstract =
            Iter.abstract_iter ~exists ark not_psi_body tr_symbols
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
          (Iter.abstract_iter ~exists ark body tr_symbols,
           base_bottom ark tr_symbols)
          ExprMap.empty
      else
        split_iter
    in
    let iter = { ark = ark; split = split_iter } in
    logf "abstract: %a" (Formula.pp ark) body;
    logf "iter: %a" pp iter;
    iter

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

  let closure split_iter =
    let ark = split_iter.ark in
    let symbols = tr_symbols split_iter in
    ExprMap.enum split_iter.split
    /@ (fun (predicate, (left, right)) ->
        let not_predicate = mk_not ark predicate in
        let left_closure =
          mk_and ark [Iter.closure_plus left; predicate]
          |> reflexive_closure ark symbols
        in
        let right_closure =
          mk_and ark [Iter.closure_plus right; not_predicate]
          |> reflexive_closure ark symbols
        in
        sequence ark symbols left_closure right_closure)
    |> BatList.of_enum
    |> mk_and ark

  let join split_iter split_iter' =
    let f _ a b = match a,b with
      | Some (a_left, a_right), Some (b_left, b_right) ->
        Some (Iter.join a_left b_left, Iter.join a_right b_right)
      | _, _ -> None
    in
    let split_join = ExprMap.merge f split_iter.split split_iter'.split in
    if ExprMap.is_empty split_join then
      lift_split
        split_iter.ark
        (Iter.join (lower_split split_iter) (lower_split split_iter))
    else
      { ark = split_iter.ark;
        split = split_join }

  let widen split_iter split_iter' =
    let f _ a b = match a,b with
      | Some (a_left, a_right), Some (b_left, b_right) ->
        Some (Iter.widen a_left b_left, Iter.widen a_right b_right)
      | _, _ -> None
    in
    let split_widen = ExprMap.merge f split_iter.split split_iter'.split in
    if ExprMap.is_empty split_widen then
      lift_split
        split_iter.ark
        (Iter.widen (lower_split split_iter) (lower_split split_iter))
    else
      { ark = split_iter.ark;
        split = split_widen }

  let equal split_iter split_iter' =
    BatEnum.for_all
      (fun ((p,(l,r)), (p',(l',r'))) ->
         Formula.equal p p'
         && Iter.equal l l'
         && Iter.equal r r')
      (BatEnum.combine
         (ExprMap.enum split_iter.split,
          ExprMap.enum split_iter'.split))
end

module Sum (A : PreDomain) (B : PreDomain) = struct
  type 'a t = Left of 'a A.t | Right of 'a B.t
  let pp formatter = function
    | Left a -> A.pp formatter a
    | Right b -> B.pp formatter b
  let show = function
    | Left a -> A.show a
    | Right b -> B.show b
  let left a = Left a
  let right b = Right b
  let closure = function
    | Left a -> A.closure a
    | Right b -> B.closure b
  let join x y = match x,y with
    | Left x, Left y -> Left (A.join x y)
    | Right x, Right y -> Right (B.join x y)
    | _, _ -> invalid_arg "Join: incompatible elements"
  let widen x y = match x,y with
    | Left x, Left y -> Left (A.widen x y)
    | Right x, Right y -> Right (B.widen x y)
    | _, _ -> invalid_arg "Widen: incompatible elements"
  let equal x y = match x,y with
    | Left x, Left y -> A.equal x y
    | Right x, Right y -> B.equal x y
    | _, _ -> invalid_arg "Equal: incompatible elements"
  let tr_symbols = function
    | Left x -> A.tr_symbols x
    | Right x -> B.tr_symbols x
end
