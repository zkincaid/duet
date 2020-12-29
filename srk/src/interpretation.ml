open Syntax
open BatPervasives

exception Divide_by_zero

module QQArray = struct
  module Map = BatMap.Make(QQ)
  type t = {stores : QQ.t Map.t; def : QQ.t}
  let create def = {stores=Map.empty;def}
  let add a i v = {stores=(Map.add i v a.stores);def=a.def}
  let select a i = Map.find_default a.def i a.stores
  let equal a b = 
    let sub a b = 
      Map.fold (fun k v eq -> QQ.equal v (select b k) && eq) a.stores true 
    in
    sub a b && sub b a && QQ.equal a.def b.def
  let pp formatter a =
    Format.fprintf formatter "@[(";
    SrkUtil.pp_print_enum
      ~pp_sep:(fun formatter () -> Format.fprintf formatter "@[")
      (fun formatter (k, v) ->  
         Format.fprintf formatter "%a ~> %a; @]"
           QQ.pp k
           QQ.pp v)
      formatter
      (Map.enum a.stores);
    Format.fprintf formatter "def ~> %a )@]"
      QQ.pp a.def
end

module SM = Symbol.Map
type 'a value = [ `Bool of bool | `Real of QQ.t | `Fun of ('a, typ_fo) expr
                | `Arr of QQArray.t]
type 'a interpretation =
  { srk : 'a context;
    default : symbol -> 'a value;
    mutable map : ('a value) SM.t }

let empty srk =
  { srk = srk;
    default = (fun _ -> raise Not_found);
    map = SM.empty }

let wrap ?(symbols=[]) srk f =
  { srk = srk;
    default = f;
    map = List.fold_left (fun m s -> SM.add s (f s) m) SM.empty symbols }

let add_real k v interp =
  match typ_symbol interp.srk k with
  | `TyReal | `TyInt -> { interp with map = SM.add k (`Real v) interp.map }
  | _ -> invalid_arg "add_real: constant symbol is non-arithmetic"

let add_bool k v interp =
  match typ_symbol interp.srk k with
  | `TyBool -> { interp with map = SM.add k (`Bool v) interp.map }
  | _ -> invalid_arg "add_boolean: constant symbol is non-boolean"

let add_fun k v interp =
  match typ_symbol interp.srk k with
  | `TyFun (_, _) -> { interp with map = SM.add k (`Fun v) interp.map }
  | _ -> invalid_arg "add_fun: constant symbol has arity zero"

let add k v interp =
  match typ_symbol interp.srk k, v with
  | (`TyFun (_, _), `Fun _)
  | (`TyReal, `Real _) | (`TyInt, `Real _)
  | (`TyBool, `Bool _) -> { interp with map = SM.add k v interp.map }
  | _ -> invalid_arg "add: type mis-match"

let value interp k =
  try SM.find k interp.map
  with Not_found ->
    let v = interp.default k in
    interp.map <- SM.add k v interp.map;
    v

let real interp k =
  match value interp k with
  | `Real v -> v
  | _ -> invalid_arg "real: constant symbol is not real"

let array interp k =
  match value interp k with
  | `Arr v -> v
  | _ -> invalid_arg "array: constant symbol is not arr"

let bool interp k =
  match value interp k with
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
    match typ_symbol interp.srk key, value with
    | `TyFun (params, _), `Fun body ->
      let formals =
        BatEnum.fold (fun formals i ->
            (Char.escaped (Char.chr (122 - i)))::formals)
          []
          (0 -- (List.length params - 1))
      in
      let env = List.fold_right Env.push formals Env.empty in
      Format.fprintf formatter "%a(@[%a@]) => @[<hov 1>%a@]"
        (pp_symbol interp.srk) key
        (SrkUtil.pp_print_enum Format.pp_print_string) (BatList.enum formals)
        (Expr.pp ~env interp.srk) body
    | _ ->
      Format.fprintf formatter "%a => @[<hov 1>%a@]"
        (pp_symbol interp.srk) key
        pp_val value
  in
  Format.fprintf formatter "[@[<v 0>%a@]]"
    (SrkUtil.pp_print_enum_nobox pp_elt) (SM.enum interp.map)


let enum interp = SM.enum interp.map

let unfold_app interpretation func actuals =
  let srk = interpretation.srk in
  match value interpretation func with
  | `Fun body ->
    let env =
      List.fold_right Env.push actuals Env.empty
    in
    substitute srk (Env.find env) body
  | _ ->
    invalid_arg "unfold_app: not a function symbol"

let substitute interpretation expr =
  let srk = interpretation.srk in
  rewrite srk ~up:(fun expr ->
      match destruct srk expr with
      | `App (sym, []) ->
        begin
          try
            (match value interpretation sym with
             | `Real qq -> (mk_real srk qq :> ('a, typ_fo) expr)
             | `Bool true -> (mk_true srk :> ('a, typ_fo) expr)
             | `Bool false -> (mk_false srk :> ('a, typ_fo) expr)
             | `Arr _ -> failwith "Array substitution not implemented"
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
  let cast_to_qq xs = 
    List.map (fun x -> match x with `QQ q -> q | _ -> assert false) xs
  in
  let f = function
    | `Real qq -> `QQ qq
    | `App (k, []) -> 
      begin match typ_symbol interp.srk k with
      | `TyArr -> `Arr (array interp k)
      | _ -> `QQ (real interp k)
      end
    | `App (func, args) ->
      begin match Expr.refine interp.srk (unfold_app interp func args) with
        | `Term t -> (evaluate_term interp ~env t)
        | `Formula _ ->
          invalid_arg "evaluate_term: ill-typed function application"
      end
    | `Binop (`Select, `Arr a, `QQ i) -> `QQ (QQArray.select a i)
    | `Store (`Arr a, `QQ i, `QQ v) -> `Arr (QQArray.add a i v)
    | `Var (i, _) -> 
      begin match Env.find env i with
        | `Real qq -> `QQ qq
        | `Array a -> `Arr a
        | `Bool _ -> invalid_arg "evaluate_term: ill-typed variable"
      end
    | `Add xs -> let xs = cast_to_qq xs in
      `QQ (List.fold_left QQ.add QQ.zero xs) 
    | `Mul xs -> let xs = cast_to_qq xs in 
      `QQ (List.fold_left QQ.mul QQ.one xs)
    | `Binop (`Div, _, `QQ divisor) when QQ.equal divisor QQ.zero ->
      raise Divide_by_zero
    | `Binop (`Mod, _, `QQ modulus) when QQ.equal modulus QQ.zero ->
      raise Divide_by_zero 
    | `Binop (`Div, `QQ dividend, `QQ divisor) -> `QQ (QQ.div dividend divisor)
    | `Binop (`Mod, `QQ t, `QQ modulus) -> `QQ (QQ.modulo t modulus)
    | `Unop (`Floor, `QQ t) -> `QQ (QQ.of_zz (QQ.floor t))
    | `Unop (`Neg, `QQ t) -> `QQ (QQ.negate t)
    | `Ite (cond, `QQ bthen, `QQ belse) ->
      if evaluate_formula interp ~env cond then
        `QQ bthen
      else
        `QQ belse
    | `Ite (cond, `Arr bthen, `Arr belse) ->
      if evaluate_formula interp ~env cond then
        `Arr bthen
      else
        `Arr belse
    | _ -> invalid_arg "evaluate_term: ill-typed term"
  in
  try
    Term.eval interp.srk f term
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
          begin match op, s ,t with
            | `Leq, `QQ s, `QQ t -> QQ.leq s t
            | `Eq, `QQ s, `QQ t-> QQ.equal s t
            | `Lt, `QQ s, `QQ t-> QQ.lt s t
            | `Eq, `Arr s, `Arr t -> QQArray.equal s t
            | _ -> invalid_arg "evaluate_formula: ill-formed atom"
          end
        with Divide_by_zero -> false
      end
    | `Not v -> not v
    | `Ite (cond, bthen, belse) -> if cond then bthen else belse
    | `Proposition (`App (k, [])) -> bool interp k
    | `Proposition (`App (func, args)) ->
      begin match Expr.refine interp.srk (unfold_app interp func args) with
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
    Formula.eval interp.srk f phi
  with Not_found ->
    invalid_arg "evaluate_formula: no interpretation for constant symbol"

let evaluate_term_qq interp ?(env=Env.empty) term =
  match evaluate_term interp ~env term with
  | `QQ q -> q
  | _ -> assert false


let get_context interp = interp.srk

let select_implicant interp ?(env=Env.empty) phi =
  let srk = interp.srk in
  let rec term t =
    match Term.destruct srk t with
    | `Real _ | `App (_, []) | `Var (_, _) -> (t, [])
    | `App (func, args) ->
      let (args, implicant) =
        List.fold_right (fun arg (args, impl) ->
            let (arg, arg_impl) = expr arg in
            (arg::args, arg_impl@impl))
          args
          ([], [])
      in
      (mk_app srk func args, implicant)
    | `Add xs ->
      let (summands, implicant) =
        List.fold_right
          (fun x (summands, implicant) ->
             let (x_term, x_implicant) = term x in
             (x_term::summands, x_implicant@implicant))
          xs
          ([], [])
      in
      (mk_add srk summands, implicant)
    | `Mul xs ->
      let (products, implicant) =
        List.fold_right
          (fun x (products, implicant) ->
             let (x_term, x_implicant) = term x in
             (x_term::products, x_implicant@implicant))
          xs
          ([], [])
      in
      (mk_mul srk products, implicant)
    | `Binop (op, s, t) ->
      let (s_term, s_impl) = term s in
      let (t_term, t_impl) = term t in
      let term =
        match op with
        | `Div -> mk_div srk s_term t_term
        | `Mod -> mk_mod srk s_term t_term
        | `Select -> mk_select srk s_term t_term
      in
      (term, s_impl@t_impl)
    | `Unop (op, t) ->
      let (t_term, t_impl) = term t in
      let term = match op with
        | `Floor -> mk_floor srk t_term
        | `Neg -> mk_neg srk t_term
      in
      (term, t_impl)
    | `Store (a, i, v) ->
        let (a_term, a_impl) = term a in
        let (i_term, i_impl) = term i in
        let (v_term, v_impl) = term v in
        mk_store srk a_term i_term v_term, a_impl@i_impl@v_impl
    | `Ite (cond, bthen, belse) ->
      begin match formula cond with
        | Some implicant ->
          let (t, t_implicant) = term bthen in
          (t, t_implicant@implicant)
        | None ->
          let not_cond =
            rewrite srk ~down:(nnf_rewriter srk) (mk_not srk cond)
          in
          match formula not_cond with
          | Some implicant ->
            let (t, t_implicant) = term belse in
            (t, t_implicant@implicant)
          | None -> assert false
      end
  and formula phi =
    match Formula.destruct srk phi with
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
            if (Formula.destruct srk phi) = `Tru then atoms
            else phi::atoms
          in
          begin match op, s_val, t_val with
            | `Eq, `QQ s_val, `QQ t_val when QQ.equal s_val t_val ->
              Some (cons_nontriv (mk_eq srk s_term t_term) (s_impl@t_impl))
            | `Leq, `QQ s_val, `QQ t_val when QQ.leq s_val t_val ->
              Some (cons_nontriv (mk_leq srk s_term t_term) (s_impl@t_impl))
            | `Lt, `QQ s_val, `QQ t_val when QQ.lt s_val t_val ->
              Some (cons_nontriv (mk_lt srk s_term t_term) (s_impl@t_impl))
            | `Eq, `Arr s_val, `Arr t_val when QQArray.equal s_val t_val ->
              Some (cons_nontriv (mk_eq srk s_term t_term) (s_impl@t_impl))  
            | _ -> None
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
      begin match Formula.destruct srk psi with
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
            rewrite srk ~down:(nnf_rewriter srk) (mk_not srk cond)
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
      if evaluate_formula interp ~env (mk_app srk func args) then
        let (args, implicant) =
          List.fold_right (fun arg (args, impl) ->
              let (arg, arg_impl) = expr arg in
              (arg::args, arg_impl@impl))
            args
            ([], [])
        in
        Some ((mk_app srk func args)::implicant)
      else
        None
    | `Quantify _ -> invalid_arg "select_implicant"
  and expr x =
    match Expr.refine srk x with
    | `Term t ->
      let (t_term, t_impl) = term t in
      ((t_term :> ('a,typ_fo) expr), t_impl)
    | `Formula phi ->
      if evaluate_formula interp ~env phi then
        match formula phi with
        | Some phi_impl -> ((mk_true srk :> ('a,typ_fo) expr), phi_impl)
        | None -> assert false
      else
        let not_phi = rewrite srk ~down:(nnf_rewriter srk) (mk_not srk phi) in
        match formula not_phi with
        | Some phi_impl -> ((mk_false srk :> ('a,typ_fo) expr), phi_impl)
        | None -> assert false
  in
  formula phi

let destruct_atom srk phi =
  match Formula.destruct srk phi with
  | `Atom (op, s, t) -> `Comparison (op, s, t)
  | `Proposition (`App (k, [])) ->
    `Literal (`Pos, `Const k)
  | `Proposition (`Var i) -> `Literal (`Pos, `Var i)
  | `Not psi ->
    begin match Formula.destruct srk psi with
      | `Proposition (`App (k, [])) -> `Literal (`Neg, `Const k)
      | `Proposition (`Var i) -> `Literal (`Neg, `Var i)
      | _ -> invalid_arg @@ Format.asprintf "destruct_atom: %a is not atomic" (Formula.pp srk) phi
    end
  | `Tru ->
    let zero = mk_real srk QQ.zero in
    `Comparison (`Eq, zero, zero)
  | `Fls -> `Comparison (`Eq, mk_real srk QQ.zero, mk_real srk QQ.one)
  | _ ->
    invalid_arg @@ Format.asprintf "destruct_atom: %a is not atomic" (Formula.pp srk) phi

let select_ite interp ?(env=Env.empty) expr =
  let conditions = ref [] in
  let rewriter expr =
    match destruct interp.srk expr with
    | `Ite (cond, bthen, belse) ->
      if evaluate_formula interp ~env cond then begin
        conditions := cond::(!conditions);
        bthen
      end else begin
        let cond' =
          mk_not interp.srk cond
          |> rewrite interp.srk ~down:(nnf_rewriter interp.srk)
        in
        conditions := cond'::(!conditions);
        belse
      end
    | _ -> expr
  in
  let expr' = rewrite interp.srk ~down:rewriter expr in
  (expr', !conditions)
