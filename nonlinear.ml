open Syntax
open Apak
open BatPervasives

include Log.Make(struct let name = "ark.nonlinear" end)

(* Symbolic intervals *)
module SymInterval = struct
  type 'a t = { ark : 'a context;
                upper : 'a term list;
                lower : 'a term list;
                interval : Interval.t }

  let cartesian ark f xs ys =
    ApakEnum.cartesian_product (BatList.enum xs) (BatList.enum ys)
    /@ (fun (x,y) -> f ark [x;y])
    |> BatList.of_enum

  let add x y =
    let ark = x.ark in
    { ark = ark;
      upper = cartesian ark mk_add x.upper y.lower;
      lower = cartesian ark mk_add x.lower y.lower;
      interval = Interval.add x.interval y.interval }

  let of_interval ark ivl =
    { ark = ark;
      upper = [];
      lower = [];
      interval = ivl }

  let zero ark = of_interval ark Interval.zero
  let bottom ark = of_interval ark Interval.bottom
  let top ark = of_interval ark Interval.top

  let mul_interval ivl x =
    let ark = x.ark in
    if Interval.is_nonnegative ivl then
      let upper = match Interval.upper ivl with
        | Some k when not (QQ.equal k QQ.zero) ->
          List.map (fun x -> mk_mul ark [mk_real ark k; x]) x.upper
        | _ -> []
      in
      let lower = match Interval.lower ivl with
        | Some k when not (QQ.equal k QQ.zero) ->
          List.map (fun x -> mk_mul ark [mk_real ark k; x]) x.lower
        | _ -> []
      in
      { ark = ark;
        upper = upper;
        lower = lower;
        interval = Interval.mul ivl x.interval }
    else if Interval.is_nonpositive ivl then
      let upper = match Interval.upper ivl with
        | Some k when not (QQ.equal k QQ.zero) ->
          List.map (fun x -> mk_mul ark [mk_real ark k; x]) x.lower
        | _ -> []
      in
      let lower = match Interval.lower ivl with
        | Some k when not (QQ.equal k QQ.zero) ->
          List.map (fun x -> mk_mul ark [mk_real ark k; x]) x.upper
        | _ -> []
      in
      { ark = ark;
        upper = upper;
        lower = lower;
        interval = Interval.mul ivl x.interval }
    else
      { ark = ark;
        upper = [];
        lower = [];
        interval = Interval.mul ivl x.interval }

  let meet x y =
    { ark = x.ark;
      upper = x.upper @ y.upper;
      lower = x.lower @ y.lower;
      interval = Interval.meet x.interval y.interval }

  let mul x y = meet (mul_interval x.interval y) (mul_interval y.interval x)

  let negate x =
    { ark = x.ark;
      interval = Interval.negate x.interval;
      upper = List.map (mk_neg x.ark) x.lower;
      lower = List.map (mk_neg x.ark) x.upper }

  let div x y =
    let ark = x.ark in
    match Interval.lower y.interval, Interval.upper y.interval with
    | Some a, Some b ->
      if Interval.elem QQ.zero y.interval then top ark
      else if QQ.equal a b then begin
        if QQ.lt QQ.zero a then
          { ark = ark;
            lower = List.map (fun x -> mk_div ark x (mk_real ark a)) x.lower;
            upper = List.map (fun x -> mk_div ark x (mk_real ark a)) x.upper;
            interval = Interval.div x.interval y.interval }
        else
          { ark = ark;
            lower = List.map (fun x -> mk_div ark x (mk_real ark a)) x.upper;
            upper = List.map (fun x -> mk_div ark x (mk_real ark a)) x.lower;
            interval = Interval.div x.interval y.interval }
      end else of_interval ark (Interval.div x.interval y.interval) (* todo *)
    | _, _ -> of_interval ark (Interval.div x.interval y.interval)

  let modulo x y =
    let ark = x.ark in
    let ivl = Interval.modulo x.interval y.interval in
    if Interval.equal ivl Interval.bottom then bottom ark
    else if Interval.elem QQ.zero y.interval then top ark
    else
      (* y is either strictly positive or strictly negative.  mod y is the
         same as mod |y| *)
      let y =
        if Interval.is_positive y.interval then y
        else negate y
      in
      let one_minus x = mk_sub ark (mk_real ark QQ.one) x in
      let minus_one x = mk_sub ark x (mk_real ark QQ.one) in
      if Interval.is_nonnegative x.interval then
        { ark = ark;
          interval = ivl;
          lower = [];
          upper = x.upper@(List.map minus_one y.upper) }
      else if Interval.is_nonpositive x.interval then
        { ark = ark;
          interval = ivl;
          lower = x.lower@(List.map one_minus y.upper);
          upper = [] }
      else
        { ark = ark;
          interval = ivl;
          lower = List.map one_minus y.upper;
          upper = List.map minus_one y.upper }

  let make ark lower upper interval =
    { ark = ark; lower = lower; upper = upper; interval = interval }
  let lower x = x.lower
  let upper x = x.upper
  let interval x = x.interval
  let floor x = make x.ark [] [] (Interval.floor x.interval)
end

(* Check if mul, div, and mod are registered, and register them if not *)
let ensure_symbols ark =
  List.iter
    (fun (name, typ) ->
       if not (is_registered_name ark name) then
         register_named_symbol ark name typ)
    [("mul", `TyFun ([`TyReal; `TyReal], `TyReal));
     ("inv", `TyFun ([`TyReal], `TyReal));
     ("mod", `TyFun ([`TyReal; `TyReal], `TyReal));
     ("imul", `TyFun ([`TyReal; `TyReal], `TyInt));
     ("imod", `TyFun ([`TyReal; `TyReal], `TyInt))]

let uninterpret_rewriter ark =
  ensure_symbols ark;
  let mul = get_named_symbol ark "mul" in
  let inv = get_named_symbol ark "inv" in
  let modulo = get_named_symbol ark "mod" in
  let imul = get_named_symbol ark "imul" in
  let imodulo = get_named_symbol ark "imod" in
  fun expr ->
    match destruct ark expr with
    | `Binop (`Div, x, y) ->
      begin match Term.destruct ark x, Term.destruct ark y with
        | (_, `Real k) when not (QQ.equal k QQ.zero) -> (* division by constant -> scalar mul *)
          (mk_mul ark [mk_real ark (QQ.inverse k); x] :> ('a,typ_fo) expr)
        | (`Real k, _) -> (mk_mul ark [x; mk_app ark inv [y]] :> ('a,typ_fo) expr)
        | _ -> mk_app ark mul [x; mk_app ark inv [y]]
      end
    | `Binop (`Mod, x, y) ->
      begin match Term.destruct ark y with
        | `Real k when not (QQ.equal k QQ.zero) -> expr
        | _ ->
          match expr_typ ark x, expr_typ ark y with
          | `TyInt, `TyInt -> mk_app ark imodulo [x; y]
          | _, _ -> mk_app ark modulo [x; y]
      end
    | `Mul (x::xs) ->
      let term =
        List.fold_left (fun x y ->
            match Term.destruct ark x, Term.destruct ark y with
            | `Real x, `Real y -> mk_real ark (QQ.mul x y)
            | `Real _, _ | _, `Real _ -> mk_mul ark [x; y]
            | _, _ ->
              match expr_typ ark x, expr_typ ark y with
              | `TyInt, `TyInt -> mk_app ark imul [x; y]
              | _, _ -> mk_app ark mul [x; y])
          x
          xs
      in
      (term :> ('a,typ_fo) expr)
    | _ -> expr

let interpret_rewriter ark =
  ensure_symbols ark;
  let mul = get_named_symbol ark "mul" in
  let inv = get_named_symbol ark "inv" in
  let modulo = get_named_symbol ark "mod" in
  let imul = get_named_symbol ark "imul" in
  let imodulo = get_named_symbol ark "imod" in
  let to_term expr =
    match refine ark expr with
    | `Term t -> t
    | `Formula _ -> assert false
  in
  fun expr ->
    match destruct ark expr with
    | `App (func, [x; y]) when func = mul || func = imul ->
      (mk_mul ark [to_term x; to_term y] :> ('a,typ_fo) expr)
    | `App (func, [x]) when func = inv ->
      (mk_div ark (mk_real ark QQ.one) (to_term x) :> ('a,typ_fo) expr)
    | `App (func, [x; y]) when func = modulo || func = imodulo ->
      (mk_mod ark (to_term x) (to_term y) :> ('a,typ_fo) expr)
    | _ -> expr

let interpret ark expr =
  rewrite ark ~up:(interpret_rewriter ark) expr

let uninterpret ark expr =
  rewrite ark ~up:(uninterpret_rewriter ark) expr

let linearize ark phi =
  let uninterp_phi = uninterpret ark phi in
  let (lin_phi, nonlinear) = ArkSimplify.purify ark uninterp_phi in
  if Symbol.Map.is_empty nonlinear then phi else begin
    (* Symbols that appear in nonlinear terms *)
    let symbol_list =
      Symbol.Map.fold
        (fun _ expr set ->
           symbols expr
           |> Symbol.Set.filter (fun sym ->
               let typ = typ_symbol ark sym in
               typ = `TyInt || typ = `TyReal)
           |> Symbol.Set.union set)
        nonlinear
        Symbol.Set.empty
      |> Symbol.Set.elements
    in
    let objectives = List.map (mk_const ark) symbol_list in
    match ArkZ3.optimize_box ark lin_phi objectives with
    | `Sat intervals ->
      let env =
        List.fold_left2
          (fun map sym ivl ->
             let t = mk_const ark sym in
             Symbol.Map.add sym (SymInterval.make ark [t] [t] ivl) map)
          Symbol.Map.empty
          symbol_list
          intervals
      in
      let linbound_zero =
        SymInterval.of_interval ark (Interval.const QQ.zero)
      in
      let linbound_one = SymInterval.of_interval ark (Interval.const QQ.one) in
      let linbound_minus_one =
        SymInterval.of_interval ark (Interval.const (QQ.negate QQ.one))
      in
      (* compute a symbolic interval for a term *)
      let rec linearize_term env term =
        match Term.destruct ark term with
        | `App (sym, []) ->
          (try Symbol.Map.find sym env
           with Not_found -> assert false)
        | `Real k -> SymInterval.of_interval ark (Interval.const k)
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
          begin match symbol_name ark func, List.map (refine ark) args with
            | (Some "imul", [`Term x; `Term y])
            | (Some "mul", [`Term x; `Term y]) ->
              SymInterval.mul (linearize_term env x) (linearize_term env y)
            | (Some "inv", [`Term x]) ->
              let one = SymInterval.of_interval ark (Interval.const QQ.one) in
              SymInterval.div one (linearize_term env x)
            | (Some "imod", [`Term x; `Term y])
            | (Some "mod", [`Term x; `Term y]) ->
              SymInterval.modulo (linearize_term env x) (linearize_term env y)
            | _ -> SymInterval.top ark
          end
        | `Var (_, _) | `Ite (_, _, _) -> assert false
      in
      (* conjoin symbolic intervals for all non-linear terms *)
      let bounds =
        let (_, bounds) =
          Symbol.Map.fold (fun symbol expr (env, bounds) ->
              match refine ark expr with
              | `Formula _ -> (env, bounds)
              | `Term term ->
                let term_bounds = linearize_term env term in
                let const = mk_const ark symbol in
                let lower =
                  let terms =
                    match Interval.lower (SymInterval.interval term_bounds) with
                    | Some k -> (mk_real ark k)::(SymInterval.lower term_bounds)
                    | None -> (SymInterval.lower term_bounds)
                  in
                  List.map (fun lo -> mk_leq ark lo const) terms
                  |> mk_and ark
                in
                let upper =
                  let terms =
                    match Interval.upper (SymInterval.interval term_bounds) with
                    | Some k -> (mk_real ark k)::(SymInterval.upper term_bounds)
                    | None -> (SymInterval.upper term_bounds)
                  in
                  List.map (fun hi -> mk_leq ark const hi) terms
                  |> mk_and ark
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
        mk_and ark bounds
      in
      (* Implied equations over non-linear terms *)
      let nonlinear_eqs =
        let nonlinear_defs =
          Symbol.Map.enum nonlinear
          /@ (fun (symbol, expr) ->
              match refine ark expr with
              | `Term t -> mk_eq ark (mk_const ark symbol) t
              | `Formula phi -> mk_iff ark (mk_const ark symbol) phi)
          |> BatList.of_enum
          |> mk_and ark
        in
        let hull =
          Abstract.affine_hull
            ark
            (mk_and ark [lin_phi; nonlinear_defs])
            (Symbol.Map.keys nonlinear |> BatList.of_enum)
        in
        List.map (mk_eq ark (mk_real ark QQ.zero)) hull |> mk_and ark
      in
      mk_and ark [lin_phi; bounds; nonlinear_eqs]
    | `Unsat -> mk_false ark
    | `Unknown ->
      logf ~level:`warn "linearize: optimization failed";
      lin_phi
  end
