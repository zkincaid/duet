open Syntax
open BatPervasives

exception Divide_by_zero

module SM = Symbol.Map
type 'a interpretation =
  { ark : 'a context;
    map : [ `Bool of bool | `Real of QQ.t | `Fun of ('a, typ_fo) expr ] SM.t }

let value interp k = SM.find k interp.map

let empty ark =
  { ark = ark;
    map = SM.empty }

let add_real k v interp =
  match typ_symbol interp.ark k with
  | `TyReal | `TyInt -> { interp with map = SM.add k (`Real v) interp.map }
  | _ -> invalid_arg "add_real: constant symbol is non-arithmetic"

let add_bool k v interp =
  match typ_symbol interp.ark k with
  | `TyBool -> { interp with map = SM.add k (`Bool v) interp.map }
  | _ -> invalid_arg "add_boolean: constant symbol is non-boolean"

let add_fun k v interp =
  match typ_symbol interp.ark k with
  | `TyFun (_, _) -> { interp with map = SM.add k (`Fun v) interp.map }
  | _ -> invalid_arg "add_fun: constant symbol has arity zero"

let real interp k =
  match SM.find k interp.map with
  | `Real v -> v
  | _ -> invalid_arg "real: constant symbol is not real"

let bool interp k =
  match SM.find k interp.map with
  | `Bool v -> v
  | _ -> invalid_arg "bool: constant symbol is not Boolean"

let pp formatter interp =
  let pp_val formatter = function
    | `Bool true -> Format.pp_print_string formatter "true"
    | `Bool false -> Format.pp_print_string formatter "false"
    | `Real q -> QQ.pp formatter q
    | _ -> assert false
  in
  let pp_elt formatter (key, value) =
    match typ_symbol interp.ark key, value with
    | `TyFun (params, _), `Fun body ->
      let formals =
        BatEnum.fold (fun formals i ->
            (Char.escaped (Char.chr (122 - i)))::formals)
          []
          (0 -- (List.length params - 1))
      in
      let env = List.fold_right Env.push formals Env.empty in
      Format.fprintf formatter "%a(@[%a@]) => @[<hov 1>%a@]"
        (pp_symbol interp.ark) key
        (ApakEnum.pp_print_enum Format.pp_print_string) (BatList.enum formals)
        (pp_expr ~env interp.ark) body
    | _ ->
      Format.fprintf formatter "%a => @[<hov 1>%a@]"
        (pp_symbol interp.ark) key
        pp_val value
  in
  Format.fprintf formatter "[@[<v 0>%a@]]"
    (ApakEnum.pp_print_enum_nobox pp_elt) (SM.enum interp.map)

let of_model ark model symbols =
  List.fold_left
    (fun interp k ->
       match typ_symbol ark k with
       | `TyReal | `TyInt ->
         add_real
           k
           (model#eval_real (mk_const ark k))
           interp
       | `TyBool ->
         add_bool
           k
           (model#sat (mk_const ark k))
           interp
       | `TyFun (params, ret) ->
         add_fun
           k
           (model#eval_fun k)
           interp)
    (empty ark)
    symbols

let enum interp = SM.enum interp.map

let unfold_app interpretation func actuals =
  let ark = interpretation.ark in
  match value interpretation func with
  | `Fun body ->
    let env =
      List.fold_right Env.push actuals Env.empty
    in
    substitute ark (Env.find env) body
  | _ ->
    invalid_arg "unfold_app: not a function symbol"

let substitute interpretation expr =
  let ark = interpretation.ark in
  rewrite ark ~up:(fun expr ->
      match destruct ark expr with
      | `App (sym, []) ->
        begin
          try
            (match value interpretation sym with
             | `Real qq -> (mk_real ark qq :> ('a, typ_fo) expr)
             | `Bool true -> (mk_true ark :> ('a, typ_fo) expr)
             | `Bool false -> (mk_false ark :> ('a, typ_fo) expr)
             | `Fun _ -> assert false)
          with Not_found -> expr
        end
      | `App (func, actuals) ->
        begin
          try
            unfold_app interpretation func actuals
          with Not_found -> expr
        end
      | _ -> expr)
    expr

let rec evaluate_term interp ?(env=Env.empty) term =
  let f = function
    | `Real qq -> qq
    | `App (k, []) -> real interp k
    | `App (func, args) ->
      begin match refine interp.ark (unfold_app interp func args) with
        | `Term t ->
          evaluate_term interp ~env t
        | `Formula _ ->
          invalid_arg "evaluate_term: ill-typed function application"
      end
    | `Var (i, _) ->
      begin match Env.find env i with
        | `Real qq -> qq
        | `Bool _ -> invalid_arg "evaluate_term: ill-typed variable"
      end
    | `Add xs -> List.fold_left QQ.add QQ.zero xs
    | `Mul xs -> List.fold_left QQ.mul QQ.one xs
    | `Binop (`Div, dividend, divisor) when QQ.equal divisor QQ.zero ->
      raise Divide_by_zero
    | `Binop (`Mod, t, modulus) when QQ.equal modulus QQ.zero ->
      raise Divide_by_zero
    | `Binop (`Div, dividend, divisor) -> QQ.div dividend divisor
    | `Binop (`Mod, t, modulus) -> QQ.modulo t modulus
    | `Unop (`Floor, t) -> QQ.of_zz (QQ.floor t)
    | `Unop (`Neg, t) -> QQ.negate t
    | `Ite (cond, bthen, belse) ->
      if evaluate_formula interp ~env cond then
        bthen
      else
        belse
  in
  try
    Term.eval interp.ark f term
  with Not_found ->
    invalid_arg "evaluate_term: no interpretation for constant symbol"

and evaluate_formula interp ?(env=Env.empty) phi =
  let f = function
    | `And xs -> List.for_all (fun x -> x) xs
    | `Or xs -> List.exists (fun x -> x) xs
    | `Tru -> true
    | `Fls -> false
    | `Atom (op, s, t) ->
      begin try
          let s = evaluate_term interp ~env s in
          let t = evaluate_term interp ~env t in
          begin match op with
            | `Leq -> QQ.leq s t
            | `Eq -> QQ.equal s t
            | `Lt -> QQ.lt s t
          end
        with Divide_by_zero -> false
      end
    | `Not v -> not v
    | `Ite (cond, bthen, belse) -> if cond then bthen else belse
    | `Proposition (`App (k, [])) -> bool interp k
    | `Proposition (`App (func, args)) ->
      begin match refine interp.ark (unfold_app interp func args) with
        | `Formula phi ->
          evaluate_formula interp ~env phi
        | `Term _ ->
          invalid_arg "evaluate_term: ill-typed function application"
      end
    | `Proposition (`Var i) ->
      begin match Env.find env i with
        | `Bool v -> v
        | _ -> invalid_arg "evaluate_formula: ill-typed variable"
      end
    | `Quantify (_, _, _, _) -> invalid_arg "evalutate_formula: quantifier"
  in
  try
    Formula.eval interp.ark f phi
  with Not_found ->
    invalid_arg "evaluate_formula: no interpretation for constant symbol"

let get_context interp = interp.ark

let select_implicant interp ?(env=Env.empty) phi =
  let ark = interp.ark in
  let rec term t =
    match Term.destruct ark t with
    | `Real _ | `App (_, []) | `Var (_, _) -> (t, [])
    | `App (func, args) ->
      let (args, implicant) =
        List.fold_right (fun arg (args, impl) ->
            let (arg, arg_impl) = expr arg in
            (arg::args, arg_impl@impl))
          args
          ([], [])
      in
      (mk_app ark func args, implicant)
    | `Add xs ->
      let (summands, implicant) =
        List.fold_right
          (fun x (summands, implicant) ->
             let (x_term, x_implicant) = term x in
             (x_term::summands, x_implicant@implicant))
          xs
          ([], [])
      in
      (mk_add ark summands, implicant)
    | `Mul xs ->
      let (products, implicant) =
        List.fold_right
          (fun x (products, implicant) ->
             let (x_term, x_implicant) = term x in
             (x_term::products, x_implicant@implicant))
          xs
          ([], [])
      in
      (mk_mul ark products, implicant)
    | `Binop (op, s, t) ->
      let (s_term, s_impl) = term s in
      let (t_term, t_impl) = term t in
      let term =
        match op with
        | `Div -> mk_div ark s_term t_term
        | `Mod -> mk_mod ark s_term t_term
      in
      (term, s_impl@t_impl)
    | `Unop (op, t) ->
      let (t_term, t_impl) = term t in
      let term = match op with
        | `Floor -> mk_floor ark t_term
        | `Neg -> mk_neg ark t_term
      in
      (term, t_impl)
    | `Ite (cond, bthen, belse) ->
      begin match formula cond with
        | Some implicant ->
          let (t, t_implicant) = term bthen in
          (t, t_implicant@implicant)
        | None ->
          let not_cond =
            rewrite ark ~down:(nnf_rewriter ark) (mk_not ark cond)
          in
          match formula not_cond with
          | Some implicant ->
            let (t, t_implicant) = term belse in
            (t, t_implicant@implicant)
          | None -> assert false
      end
  and formula phi =
    match Formula.destruct ark phi with
    | `Tru -> Some []
    | `Fls -> None
    | `Or disjuncts ->
      (* Find satisfied disjunct *)
      let f disjunct phi =
        match disjunct with
        | None -> formula phi
        | _ -> disjunct
      in
      List.fold_left f None disjuncts
    | `And conjuncts ->
      (* All conjuncts must be satisfied *)
      let f phi =
        match formula phi with
        | Some x -> x
        | None -> raise Not_found
      in
      (try Some (BatList.concat (List.map f conjuncts))
       with Not_found -> None)
    | `Atom (op, s, t) ->
      let (s_term, s_impl) = term s in
      let (t_term, t_impl) = term t in
      begin
        try
          let s_val = evaluate_term interp ~env s_term in
          let t_val = evaluate_term interp ~env t_term in
          let cons_nontriv phi atoms =
            if (Formula.destruct ark phi) = `Tru then atoms
            else phi::atoms
          in
          begin match op with
            | `Eq when QQ.equal s_val t_val ->
              Some (cons_nontriv (mk_eq ark s_term t_term) (s_impl@t_impl))
            | `Leq when QQ.leq s_val t_val ->
              Some (cons_nontriv (mk_leq ark s_term t_term) (s_impl@t_impl))
            | `Lt when QQ.lt s_val t_val ->
              Some (cons_nontriv (mk_lt ark s_term t_term) (s_impl@t_impl))
            | _ ->
              None
          end
        with Divide_by_zero -> None
      end
    | `Proposition (`App (p, [])) ->
      if bool interp p then Some [phi]
      else None
    | `Proposition (`Var v) ->
      begin match Env.find env v with
        | `Bool true -> Some [phi]
        | `Bool _ -> None
        | _ -> invalid_arg "select_implicant: ill-typed propositional variable"
      end
    | `Not psi ->
      begin match Formula.destruct ark psi with
        | `Proposition (`App (p, [])) ->
          if not (bool interp p) then
            Some [phi]
          else
            None
        | `Proposition (`Var v) ->
          begin match Env.find env v with
            | `Bool false -> Some [phi]
            | `Bool _ -> None
            | _ ->
              invalid_arg "select_implicant: ill-typed propositional variable"
          end
        | _ -> invalid_arg "select_implicant: negation"
      end
    | `Ite (cond, bthen, belse) ->
      begin match formula cond with
        | Some cond_implicant ->
          begin match formula bthen with
            | Some bthen_implicant -> Some (cond_implicant@bthen_implicant)
            | None -> None
          end
        | None ->
          let not_cond =
            rewrite ark ~down:(nnf_rewriter ark) (mk_not ark cond)
          in
          match formula not_cond with
          | Some cond_implicant ->
            begin match formula belse with
              | Some belse_implicant -> Some (cond_implicant@belse_implicant)
              | None -> None
            end
          | None -> None
      end
    | `Proposition (`App (func, args)) ->
      if evaluate_formula interp ~env (mk_app ark func args) then
        let (args, implicant) =
          List.fold_right (fun arg (args, impl) ->
              let (arg, arg_impl) = expr arg in
              (arg::args, arg_impl@impl))
            args
            ([], [])
        in
        Some ((mk_app ark func args)::implicant)
      else
        None
    | `Quantify _ -> invalid_arg "select_implicant"
  and expr x =
    match refine ark x with
    | `Term t ->
      let (t_term, t_impl) = term t in
      ((t_term :> ('a,typ_fo) expr), t_impl)
    | `Formula phi ->
      if evaluate_formula interp ~env phi then
        match formula phi with
        | Some phi_impl -> ((mk_true ark :> ('a,typ_fo) expr), phi_impl)
        | None -> assert false
      else
        let not_phi = rewrite ark ~down:(nnf_rewriter ark) (mk_not ark phi) in
        match formula not_phi with
        | Some phi_impl -> ((mk_false ark :> ('a,typ_fo) expr), phi_impl)
        | None -> assert false
  in
  formula phi

let destruct_atom ark phi =
  match Formula.destruct ark phi with
  | `Atom (op, s, t) -> `Comparison (op, s, t)
  | `Proposition (`App (k, [])) ->
    `Literal (`Pos, `Const k)
  | `Proposition (`Var i) -> `Literal (`Pos, `Var i)
  | `Not psi ->
    begin match Formula.destruct ark psi with
      | `Proposition (`App (k, [])) -> `Literal (`Neg, `Const k)
      | `Proposition (`Var i) -> `Literal (`Neg, `Var i)
      | _ -> invalid_arg "destruct_atomic: not atomic"
    end
  | `Tru ->
    let zero = mk_real ark QQ.zero in
    `Comparison (`Eq, zero, zero)
  | `Fls -> `Comparison (`Eq, mk_real ark QQ.zero, mk_real ark QQ.one)
  | _ ->
    invalid_arg "destruct_atomic: not atomic"
