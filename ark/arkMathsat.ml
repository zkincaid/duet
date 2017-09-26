open Syntax
open Batteries
open Mathsat

type 'a gexpr = ('a, typ_fo) expr

let of_msat ark msat_env sym_of_decl expr =
  let term expr =
    match Expr.refine ark expr with
    | `Term t -> t
    | _ -> invalid_arg "of_mathsat.term"
  in
  let formula expr =
    match Expr.refine ark expr with
    | `Formula phi -> phi
    | _ -> invalid_arg "of_mathsat.formula"
  in
  let rec go expr =
    match Mathsat.msat_destruct msat_env expr with
    | `Tru -> (mk_true ark :> 'a gexpr)
    | `Fls -> (mk_false ark :> 'a gexpr)
    | `Real qq -> (mk_real ark (Mpqf.of_mpq qq) :> 'a gexpr)
    | `Add sum -> (mk_add ark (List.map (term % go) sum) :> 'a gexpr)
    | `Mul product -> (mk_mul ark (List.map (term % go) product) :> 'a gexpr)
    | `Unop (`Floor, t) -> (mk_floor ark (term (go t)) :> 'a gexpr)
    | `Atom (op, s, t) ->
      let (s, t) = (term (go s), term (go t)) in
      begin match op with
        | `Eq -> (mk_eq ark s t :> 'a gexpr)
        | `Leq -> (mk_leq ark s t :> 'a gexpr)
      end
    | `And conjuncts ->
      (mk_and ark (List.map (formula % go) conjuncts) :> 'a gexpr)
    | `Or disjuncts ->
      (mk_or ark (List.map (formula % go) disjuncts) :> 'a gexpr)
    | `Iff (phi, psi) ->
      (mk_iff ark (formula (go phi)) (formula (go psi)) :> 'a gexpr)
    | `Not phi -> (mk_not ark (formula (go phi)) :> 'a gexpr)
    | `Ite (cond, bthen, belse) ->
      mk_ite ark (formula (go cond)) (go bthen) (go belse)
    | `App (decl, args) ->
      mk_app ark (sym_of_decl decl) (List.map go args)
  in
  go expr

let rec msat_of_expr ark msat decl_of_sym expr  =
  match Expr.refine ark expr with
  | `Term t -> msat_of_term ark msat decl_of_sym t
  | `Formula phi -> msat_of_formula ark msat decl_of_sym phi

and msat_of_term (ark : 'a context) msat decl_of_sym (term : 'a term) =
  let alg = function
    | `Real qq -> 
      begin match QQ.to_zz qq with
        | Some zz -> Mathsat.msat_make_number msat (ZZ.show zz)
        | None -> Mathsat.msat_make_number msat (QQ.show qq)
      end
    | `App (sym, []) ->
      Mathsat.msat_make_constant msat (decl_of_sym sym)

    | `App (func, args) ->
      Mathsat.msat_make_uf msat
        (decl_of_sym func)
        (List.map (msat_of_expr ark msat decl_of_sym) args)

    | `Var (_, _) -> invalid_arg "msat_of: var"
    | `Add [] -> Mathsat.msat_make_number msat "0"
    | `Add (x::xs) -> List.fold_left (Mathsat.msat_make_plus msat) x xs
    | `Mul [] -> Mathsat.msat_make_number msat "1"
    | `Mul (x::xs) -> List.fold_left (Mathsat.msat_make_times msat) x xs
    | `Binop (`Div, s, t) -> invalid_arg "msat_of: division"
    | `Binop (`Mod, s, t) -> invalid_arg "msat_of: modulo"
    | `Unop (`Floor, t) -> Mathsat.msat_make_floor msat t
    | `Unop (`Neg, t) ->
      Mathsat.msat_make_times msat (Mathsat.msat_make_number msat "-1") t
    | `Ite (cond, bthen, belse) ->
      Mathsat.msat_make_term_ite msat 
        (msat_of_formula ark msat decl_of_sym cond)
        bthen
        belse
  in
  Term.eval ark alg term

and msat_of_formula ark msat decl_of_sym phi =
  let of_term = msat_of_term ark msat decl_of_sym in
  let alg = function
    | `Tru -> Mathsat.msat_make_true msat
    | `Fls -> Mathsat.msat_make_false msat
    | `And [] -> Mathsat.msat_make_true msat
    | `And (x::xs) -> List.fold_left (Mathsat.msat_make_and msat) x xs
    | `Or [] -> Mathsat.msat_make_true msat
    | `Or (x::xs) -> List.fold_left (Mathsat.msat_make_or msat) x xs
    | `Not phi -> Mathsat.msat_make_not msat phi
    | `Quantify (_, _, _, _) -> invalid_arg "msat_of: quantifier"

    | `Atom (`Eq, s, t) ->
      Mathsat.msat_make_equal msat (of_term s) (of_term t)
    | `Atom (`Leq, s, t) ->
      Mathsat.msat_make_leq msat (of_term s) (of_term t)
    | `Atom (`Lt, s, t) -> 
      Mathsat.msat_make_not msat
        (Mathsat.msat_make_leq msat (of_term t) (of_term s))
    | `Proposition (`Var _) -> invalid_arg "msat_of: variable"
    | `Proposition (`App (sym, [])) ->
      Mathsat.msat_make_constant msat (decl_of_sym sym)
    | `Proposition (`App (predicate, args)) ->
      Mathsat.msat_make_uf msat
        (decl_of_sym predicate)
        (List.map (msat_of_expr ark msat decl_of_sym) args)
    | `Ite (cond, bthen, belse) ->
      Mathsat.msat_make_term_ite msat cond bthen belse
  in
  Formula.eval ark alg phi

class ['a] msat_solver (ark : 'a context) =
  let msat_config =
    let cfg = msat_create_config () in
    msat_set_option cfg "model_generation" "true";
    cfg
  in      
  let msat = msat_create_env msat_config in
  let msat_bool = Mathsat.msat_get_bool_type msat in
  let msat_int = Mathsat.msat_get_integer_type msat in
  let msat_rational = Mathsat.msat_get_rational_type msat in
  let rec msat_type = function
    | `TyInt -> msat_int
    | `TyReal -> msat_rational
    | `TyBool -> msat_bool
    | `TyFun (args, ret) ->
      Mathsat.msat_get_function_type msat
        (List.map msat_type (args :> typ list))
        (msat_type (ret :> typ))
  in
  let decl_table = Hashtbl.create 991 in
  let decl_of_sym =
    Memo.memo (fun sym ->
        let name = show_symbol ark sym in
        let typ = msat_type (typ_symbol ark sym) in
        let decl = Mathsat.msat_declare_function msat name typ in
        Hashtbl.add decl_table (Mathsat.msat_decl_id decl) sym;
        decl)
  in
  let of_formula = msat_of_formula ark msat decl_of_sym in
  let of_term = msat_of_term ark msat decl_of_sym in
  object(self)
    method add formulas =
      formulas |> List.iter (fun phi ->
          Mathsat.msat_assert_formula msat (of_formula phi))
    method push () =
      Mathsat.msat_push_backtrack_point msat
    method pop num =
      if num < 0 then invalid_arg "msat_solver#pop: must be >= 0"
      else if num = 0 then ()
      else (Mathsat.msat_pop_backtrack_point msat; self#pop (num - 1))
    method reset () =
      Mathsat.msat_reset_env msat
    method check : 'a formula list -> [`Sat |`Unsat|`Unknown] =
      fun assumptions ->
        self#push ();
        self#add assumptions;
        let result = Mathsat.msat_solve msat in
        self#pop 1;
        match result with
        | Mathsat.Sat -> `Sat
        | Mathsat.Unsat -> `Unsat
        | Mathsat.Unknown -> `Unknown
    method to_string () = "<<msat_solver>>"
    method get_model : unit -> [`Sat of 'a smt_model | `Unknown | `Unsat] =
      fun () ->
        match Mathsat.msat_solve msat with
        | Mathsat.Sat ->
          let model = Mathsat.msat_get_model msat in
          let eval t = Mathsat.msat_model_eval model (of_term t) in
          let m =
            object(self)
              method eval_int term =
                let error () = invalid_arg "eval_int: not an integer term" in
                match Mathsat.msat_destruct msat (eval term) with
                | `Real qq -> begin match QQ.to_zz (Mpqf.of_mpq qq) with
                    | Some zz -> zz
                    | None -> error ()
                  end
                | _ -> error ()
              method eval_real term =
                match Mathsat.msat_destruct msat (eval term) with
                | `Real qq -> (Mpqf.of_mpq qq)
                | _ -> invalid_arg "eval_real: not a real term"
                         
              method sat phi =
                let eval = Mathsat.msat_model_eval model (of_formula phi) in
                match Mathsat.msat_destruct msat eval with
                | `Tru -> true
                | `Fls -> false
                | _ -> invalid_arg "sat: not a formula"
                         
              method to_string () = "<<msat_model>>"

              method eval_fun symbol =
                (failwith "MathSAT eval_fun not supported" :> ('a,'b) expr)
            end
          in
          `Sat m
        | Mathsat.Unsat -> `Unsat
        | Mathsat.Unknown -> `Unknown
    method get_unsat_core (xs : ('a formula) list) : [ `Sat | `Unsat of ('a formula) list | `Unknown ] =
      failwith "MathSAT get_unsat_core not supported"
  end

let mk_solver ark = new msat_solver ark
