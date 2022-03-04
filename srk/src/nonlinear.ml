open Syntax
open BatPervasives
module Term = ArithTerm

include Log.Make(struct let name = "srk.nonlinear" end)

(* Symbolic intervals *)
module SymInterval = struct
  type 'a t = { srk : 'a context;
                upper : 'a arith_term list;
                lower : 'a arith_term list;
                interval : Interval.t }

  let cartesian srk f xs ys =
    SrkUtil.cartesian_product (BatList.enum xs) (BatList.enum ys)
    /@ (fun (x,y) -> f srk [x;y])
    |> BatList.of_enum

  let add x y =
    let srk = x.srk in
    { srk = srk;
      upper = cartesian srk mk_add x.upper y.lower;
      lower = cartesian srk mk_add x.lower y.lower;
      interval = Interval.add x.interval y.interval }

  let of_interval srk ivl =
    { srk = srk;
      upper = [];
      lower = [];
      interval = ivl }

  let bottom srk = of_interval srk Interval.bottom
  let top srk = of_interval srk Interval.top

  let mul_interval ivl x =
    let srk = x.srk in
    if Interval.is_nonnegative ivl then
      let upper = match Interval.upper ivl with
        | Some k when not (QQ.equal k QQ.zero) ->
          List.map (fun x -> mk_mul srk [mk_real srk k; x]) x.upper
        | _ -> []
      in
      let lower = match Interval.lower ivl with
        | Some k when not (QQ.equal k QQ.zero) ->
          List.map (fun x -> mk_mul srk [mk_real srk k; x]) x.lower
        | _ -> []
      in
      { srk = srk;
        upper = upper;
        lower = lower;
        interval = Interval.mul ivl x.interval }
    else if Interval.is_nonpositive ivl then
      let upper = match Interval.upper ivl with
        | Some k when not (QQ.equal k QQ.zero) ->
          List.map (fun x -> mk_mul srk [mk_real srk k; x]) x.lower
        | _ -> []
      in
      let lower = match Interval.lower ivl with
        | Some k when not (QQ.equal k QQ.zero) ->
          List.map (fun x -> mk_mul srk [mk_real srk k; x]) x.upper
        | _ -> []
      in
      { srk = srk;
        upper = upper;
        lower = lower;
        interval = Interval.mul ivl x.interval }
    else
      { srk = srk;
        upper = [];
        lower = [];
        interval = Interval.mul ivl x.interval }

  let meet x y =
    { srk = x.srk;
      upper = x.upper @ y.upper;
      lower = x.lower @ y.lower;
      interval = Interval.meet x.interval y.interval }

  let mul x y = meet (mul_interval x.interval y) (mul_interval y.interval x)

  let negate x =
    { srk = x.srk;
      interval = Interval.negate x.interval;
      upper = List.map (mk_neg x.srk) x.lower;
      lower = List.map (mk_neg x.srk) x.upper }

  let div x y =
    let srk = x.srk in
    match Interval.lower y.interval, Interval.upper y.interval with
    | Some a, Some b ->
      if Interval.elem QQ.zero y.interval then top srk
      else if QQ.equal a b then begin
        if QQ.lt QQ.zero a then
          { srk = srk;
            lower = List.map (fun x -> mk_div srk x (mk_real srk a)) x.lower;
            upper = List.map (fun x -> mk_div srk x (mk_real srk a)) x.upper;
            interval = Interval.div x.interval y.interval }
        else
          { srk = srk;
            lower = List.map (fun x -> mk_div srk x (mk_real srk a)) x.upper;
            upper = List.map (fun x -> mk_div srk x (mk_real srk a)) x.lower;
            interval = Interval.div x.interval y.interval }
      end else of_interval srk (Interval.div x.interval y.interval) (* todo *)
    | _, _ -> of_interval srk (Interval.div x.interval y.interval)

  let modulo x y =
    let srk = x.srk in
    let ivl = Interval.modulo x.interval y.interval in
    if Interval.equal ivl Interval.bottom then bottom srk
    else if Interval.elem QQ.zero y.interval then top srk
    else
      (* y is either strictly positive or strictly negative.  mod y is the
         same as mod |y| *)
      let y =
        if Interval.is_positive y.interval then y
        else negate y
      in
      let one_minus x = mk_sub srk (mk_real srk QQ.one) x in
      let minus_one x = mk_sub srk x (mk_real srk QQ.one) in
      if Interval.is_nonnegative x.interval then
        { srk = srk;
          interval = ivl;
          lower = [];
          upper = x.upper@(List.map minus_one y.upper) }
      else if Interval.is_nonpositive x.interval then
        { srk = srk;
          interval = ivl;
          lower = x.lower@(List.map one_minus y.upper);
          upper = [] }
      else
        { srk = srk;
          interval = ivl;
          lower = List.map one_minus y.upper;
          upper = List.map minus_one y.upper }

  let make srk lower upper interval =
    { srk = srk; lower = lower; upper = upper; interval = interval }
  let lower x = x.lower
  let upper x = x.upper
  let interval x = x.interval
  let floor x = make x.srk [] [] (Interval.floor x.interval)

  let join x y =
    let interval = Interval.join x.interval y.interval in
    let lower = List.filter (fun b -> List.mem b y.lower) x.lower in
    let upper = List.filter (fun b -> List.mem b y.upper) x.upper in
    { srk = x.srk; lower; upper; interval }
end

(* Check if mul, div, mod, pow, log are registered, and register them if not *)
let ensure_symbols srk =
  List.iter
    (fun (name, typ) ->
       if not (is_registered_name srk name) then
         register_named_symbol srk name typ)
    [("mul", `TyFun ([`TyReal; `TyReal], `TyReal));
     ("inv", `TyFun ([`TyReal], `TyReal));
     ("mod", `TyFun ([`TyReal; `TyReal], `TyReal));
     ("imul", `TyFun ([`TyReal; `TyReal], `TyInt));
     ("imod", `TyFun ([`TyReal; `TyReal], `TyInt));
     ("pow", (`TyFun ([`TyReal; `TyReal], `TyReal)));
     ("log", (`TyFun ([`TyReal; `TyReal], `TyReal)));
     ("is_int", `TyFun ([`TyReal], `TyBool))
    ]

let uninterpret_rewriter srk =
  ensure_symbols srk;
  let mul = get_named_symbol srk "mul" in
  let inv = get_named_symbol srk "inv" in
  let modulo = get_named_symbol srk "mod" in
  let imul = get_named_symbol srk "imul" in
  let imodulo = get_named_symbol srk "imod" in
  fun expr ->
    match destruct srk expr with
    | `Binop (`Div, x, y) ->
      begin match Term.destruct srk x, Term.destruct srk y with
        | (_, `Real k) when not (QQ.equal k QQ.zero) ->
          (* division by constant -> scalar mul *)
          (mk_mul srk [mk_real srk (QQ.inverse k); x] :> ('a,typ_fo) expr)
        | (`Real _, _) -> (mk_mul srk [x; mk_app srk inv [y]] :> ('a,typ_fo) expr)
        | _ -> mk_app srk mul [x; mk_app srk inv [y]]
      end
    | `Binop (`Mod, x, y) ->
      begin match Term.destruct srk y with
        | `Real k when (not (QQ.equal k QQ.zero)
                        && QQ.to_zz k != None
                        && Term.typ srk x = `TyInt) -> expr

        | _ ->
          match expr_typ srk x, expr_typ srk y with
          | `TyInt, `TyInt -> mk_app srk imodulo [x; y]
          | _, _ -> mk_app srk modulo [x; y]
      end

    | `Mul xs ->
      let (coeff, ys) =
        List.fold_left (fun (coeff, ys) y ->
            match Term.destruct srk y with
            | `Real k -> (QQ.mul coeff k, ys)
            | _ -> (coeff, y::ys))
          (QQ.one, [])
          xs
      in
      let coeff_term = mk_real srk coeff in
      let term =
        match ys with
        | [] -> coeff_term
        | [y] -> mk_mul srk [coeff_term; y]
        | (y::ys) ->
          let product =
            List.fold_left (fun x y ->
                match expr_typ srk x, expr_typ srk y with
                | `TyInt, `TyInt -> mk_app srk imul [y; x]
                | _, _ -> mk_app srk mul [y; x])
              y
              ys
          in
          mk_mul srk [coeff_term; product]
      in
      (term :> ('a,typ_fo) expr)
    | _ -> expr

let interpret_rewriter srk =
  ensure_symbols srk;
  let mul = get_named_symbol srk "mul" in
  let inv = get_named_symbol srk "inv" in
  let modulo = get_named_symbol srk "mod" in
  let imul = get_named_symbol srk "imul" in
  let imodulo = get_named_symbol srk "imod" in
  let to_term expr =
    match Expr.refine srk expr with
    | `ArithTerm t -> t
    | `ArrTerm _ 
    | `Formula _ -> assert false
  in
  fun expr ->
    match destruct srk expr with
    | `App (func, [x; y]) when func = mul || func = imul ->
       (mk_mul srk [to_term x; to_term y] :> ('a,typ_fo) expr)
    | `App (func, [x]) when func = inv ->
       (mk_div srk (mk_real srk QQ.one) (to_term x) :> ('a,typ_fo) expr)
    | `App (func, [x; y]) when func = modulo || func = imodulo ->
       (mk_mod srk (to_term x) (to_term y) :> ('a,typ_fo) expr)
    | _ -> expr

let interpret srk expr =
  rewrite srk ~up:(interpret_rewriter srk) expr

let uninterpret srk expr =
  rewrite srk ~up:(uninterpret_rewriter srk) expr

let linearize srk phi =
  let uninterp_phi = uninterpret srk phi in
  let (lin_phi, nonlinear) = SrkSimplify.purify srk uninterp_phi in
  if Symbol.Map.is_empty nonlinear then
    phi
  else begin
    (* Symbols that appear in nonlinear terms *)
    let symbol_list =
      Symbol.Map.fold
        (fun _ expr set ->
           symbols expr
           |> Symbol.Set.filter (fun sym ->
               let typ = typ_symbol srk sym in
               typ = `TyInt || typ = `TyReal)
           |> Symbol.Set.union set)
        nonlinear
        Symbol.Set.empty
      |> Symbol.Set.elements
    in
    let objectives = List.map (mk_const srk) symbol_list in
    match SrkZ3.optimize_box srk lin_phi objectives with
    | `Sat intervals ->
      let env =
        List.fold_left2
          (fun map sym ivl ->
             let t = mk_const srk sym in
             Symbol.Map.add sym (SymInterval.make srk [t] [t] ivl) map)
          Symbol.Map.empty
          symbol_list
          intervals
      in
      let linbound_zero =
        SymInterval.of_interval srk (Interval.const QQ.zero)
      in
      let linbound_one = SymInterval.of_interval srk (Interval.const QQ.one) in
      let linbound_minus_one =
        SymInterval.of_interval srk (Interval.const (QQ.negate QQ.one))
      in
      (* compute a symbolic interval for a term *)
      let rec linearize_term env term =
        match Term.destruct srk term with
        | `App (sym, []) ->
          (try Symbol.Map.find sym env
           with Not_found -> assert false)
        | `Real k -> SymInterval.of_interval srk (Interval.const k)
        | `Add sum ->
          List.fold_left
            (fun linbound t -> SymInterval.add linbound (linearize_term env t))
            linbound_zero
            sum
        | `Mul prod ->
          List.fold_left
            (fun linbound t -> SymInterval.mul linbound (linearize_term env t))
            linbound_one
            prod
        | `Binop (`Div, x, y) ->
          SymInterval.div (linearize_term env x) (linearize_term env y)
        | `Binop (`Mod, x, y) ->
          SymInterval.modulo (linearize_term env x) (linearize_term env y)
        | `Unop (`Floor, x) -> SymInterval.floor (linearize_term env x)
        | `Unop (`Neg, x) ->
          SymInterval.mul linbound_minus_one (linearize_term env x)
        | `App (func, args) ->
          begin match symbol_name srk func, List.map (Expr.refine srk) args with
            | (Some "imul", [`ArithTerm x; `ArithTerm y])
            | (Some "mul", [`ArithTerm x; `ArithTerm y]) ->
              SymInterval.mul (linearize_term env x) (linearize_term env y)
            | (Some "inv", [`ArithTerm x]) ->
              let one = SymInterval.of_interval srk (Interval.const QQ.one) in
              SymInterval.div one (linearize_term env x)
            | (Some "imod", [`ArithTerm x; `ArithTerm y])
            | (Some "mod", [`ArithTerm x; `ArithTerm y]) ->
              SymInterval.modulo (linearize_term env x) (linearize_term env y)
            | (Some "_floor", [`ArithTerm x]) ->
              SymInterval.floor (linearize_term env x)
            | _ -> SymInterval.top srk
          end
        | `Ite (_, x, y) ->
          SymInterval.join (linearize_term env x) (linearize_term env y)
        | `Var (_, _) -> assert false
        | `Select _ -> SymInterval.top srk
      in
      (* conjoin symbolic intervals for all non-linear terms *)
      let bounds =
        let (_, bounds) =
          Symbol.Map.fold (fun symbol expr (env, bounds) ->
              match Expr.refine srk expr with
              | `Formula _ -> (env, bounds)
              | `ArrTerm _ -> (env, bounds)
              | `ArithTerm term ->
                let term_bounds = linearize_term env term in
                let const = mk_const srk symbol in
                let lower =
                  let terms =
                    match Interval.lower (SymInterval.interval term_bounds) with
                    | Some k -> (mk_real srk k)::(SymInterval.lower term_bounds)
                    | None -> (SymInterval.lower term_bounds)
                  in
                  List.map (fun lo -> mk_leq srk lo const) terms
                  |> mk_and srk
                in
                let upper =
                  let terms =
                    match Interval.upper (SymInterval.interval term_bounds) with
                    | Some k -> (mk_real srk k)::(SymInterval.upper term_bounds)
                    | None -> (SymInterval.upper term_bounds)
                  in
                  List.map (fun hi -> mk_leq srk const hi) terms
                  |> mk_and srk
                in
                let ivl =
                  if Symbol.Map.mem symbol env then
                    SymInterval.meet
                      term_bounds
                      (Symbol.Map.find symbol env)
                  else
                    term_bounds
                in
                (Symbol.Map.add symbol ivl env, lower::(upper::bounds)))
            nonlinear
            (env, [])
        in
        mk_and srk bounds
      in
      (* Implied equations over non-linear terms *)
      let nonlinear_eqs =
        let nonlinear_defs =
          Symbol.Map.enum nonlinear
          /@ (fun (symbol, expr) ->
              match Expr.refine srk expr with
              | `ArithTerm t -> mk_eq srk (mk_const srk symbol) t
              | `ArrTerm t -> mk_arr_eq srk (mk_const srk symbol) t
              | `Formula phi -> mk_iff srk (mk_const srk symbol) phi)
          |> BatList.of_enum
          |> mk_and srk
        in
        let hull =
          Abstract.affine_hull
            srk
            (mk_and srk [lin_phi; nonlinear_defs])
            (Symbol.Map.keys nonlinear |> BatList.of_enum)
        in
        List.map (mk_eq srk (mk_real srk QQ.zero)) hull |> mk_and srk
      in
      mk_and srk [lin_phi; bounds; nonlinear_eqs]
    | `Unsat -> mk_false srk
    | `Unknown ->
      logf ~level:`warn "linearize: optimization failed";
      lin_phi
  end

let mk_log srk base x =
  let pow = get_named_symbol srk "pow" in
  match Term.destruct srk base, Term.destruct srk x with
  | `Real b, `Real x when (QQ.lt QQ.one b) && (QQ.equal x QQ.one) ->
    mk_real srk QQ.zero
  | `Real b, `Real x when (QQ.lt QQ.one b) && (QQ.equal x b) ->
    mk_real srk QQ.one
  | _, `App (p, [base'; t]) when p = pow && Expr.equal (base :> ('a,typ_fo) expr) base' ->
    (Expr.arith_term_of srk t)
  | _, _ ->
    let log = get_named_symbol srk "log" in
    mk_app srk log [base; x]

let rec mk_pow srk base x =
  let log = get_named_symbol srk "log" in
  match Term.destruct srk base with
  | `Real b when QQ.equal b QQ.one ->
    mk_real srk QQ.one
  | `Real b when QQ.lt b QQ.zero ->
    let pow = mk_pow srk (mk_real srk (QQ.negate b)) x in
    mk_ite
      srk
      (mk_eq srk (mk_mod srk x (mk_real srk (QQ.of_int 2))) (mk_real srk QQ.zero))
      pow
      (mk_neg srk pow)
  | `Real b when QQ.lt QQ.zero b && QQ.lt b QQ.one ->
    (* b^x when 0<b<1 yields 1/[(1/b)^x] *)
    mk_div srk
      (mk_real srk QQ.one)
      (mk_pow srk (mk_div srk (mk_real srk QQ.one) base) x)
    (* OR: b^x when 0<b<1 yields (1/b)^(-x) *)
    (*(mk_pow srk (mk_div srk (mk_real srk QQ.one) base) (mk_neg srk x))*)
  | _ ->
    match Term.destruct srk x with
    | `Real power ->
      begin match QQ.to_int power with
        | Some power -> Syntax.mk_pow srk base power
        | None ->
          let pow = get_named_symbol srk "pow" in
        mk_app srk pow [base; x]
      end

    | `Add xs ->
      mk_mul srk (List.map (mk_pow srk base) xs)

    | `Unop (`Neg, x) ->
      mk_div srk (mk_real srk QQ.one) (mk_pow srk base x)

    | `App (p, [base'; t]) when p = log && Expr.equal (base :> ('a,typ_fo) expr) base' ->
      (* TODO: Applies only when t >= 0 *)
      (Expr.arith_term_of srk t)

    | _ ->
      let pow = get_named_symbol srk "pow" in
      mk_app srk pow [base; x]

let optimize_box ?(context=Z3.mk_context []) srk phi objectives =
  let phi = SrkSimplify.simplify_terms srk phi in
  let objective_symbols =
    List.map (fun t ->
        mk_const srk (mk_symbol srk (Term.typ srk t :> typ)))
      objectives
  in
  let objective_eqs =
    List.map2 (fun o o' -> mk_eq srk o o') objectives objective_symbols
  in
  let lin_phi =
    linearize srk (mk_and srk (phi::objective_eqs))
  in
  Log.time "optimize"
    (SrkZ3.optimize_box ~context srk lin_phi) objective_symbols

let simplify_terms_rewriter srk =
  ensure_symbols srk;
  let pow = get_named_symbol srk "pow" in
  let log = get_named_symbol srk "log" in
  fun expr ->
    match destruct srk expr with
    | `App (func, [x; y]) when func = pow ->
      (mk_pow srk (Expr.arith_term_of srk x) (Expr.arith_term_of srk y) :> ('a, typ_fo) expr)
    | `App (func, [x; y]) when func = log ->
      (mk_log srk (Expr.arith_term_of srk x) (Expr.arith_term_of srk y) :> ('a, typ_fo) expr)
    | _ -> expr

let simplify_terms srk expr =
  rewrite srk ~up:(simplify_terms_rewriter srk) expr

let simplify_term srk expr =
  rewrite srk ~up:(simplify_terms_rewriter srk) expr
