open Syntax
open Iteration
module V = Linear.QQVector
module M = Linear.QQMatrix
module Z = Linear.ZZVector
module H = Abstract
include Log.Make(struct let name = "srk.array:" end)

type 'a t = 'a formula

(*let projection = failwith "todo 1"*)

  let dataless_termalg_helper srk obj =
  match obj with
  | `Real qq -> mk_real srk qq
  | `Add summands -> mk_add srk summands
  | `Mul products -> mk_mul srk products
  | `Binop (`Div, s, t) -> mk_div srk s t
  | `Binop (`Mod, s, t) -> mk_mod srk s t
  | `Unop (`Floor, t) -> mk_floor srk t
  | `Unop (`Neg, t) -> mk_neg srk t
  | `Var (ind, `TyInt) -> mk_var srk ind `TyInt 
  | `Ite (_, _, _) -> failwith "TOOD"
  | `App (sym, []) -> mk_const srk sym (* case may be missing from data version *)
  | _ -> failwith "not in scope of logical fragment"

let dataless_formalg_helper srk termalg obj =
  match obj with
  | `Tru -> mk_true srk
  | `Fls -> mk_false srk
  | `Atom (`Eq, x, y) -> mk_eq srk (Term.eval srk termalg x) (Term.eval srk termalg y)
  | `Atom (`Leq, x, y) -> mk_leq srk (Term.eval srk termalg x) (Term.eval srk termalg y)
  | `Atom (`Lt, x, y) -> mk_lt srk (Term.eval srk termalg x) (Term.eval srk termalg y)
  | `And cons -> mk_and srk cons
  | `Or disj -> mk_or srk disj
  | `Ite (cond, bthen, belse) -> mk_ite srk cond bthen belse
  | `Not f -> mk_not srk f           
  |`Proposition (`App (p, [expr])) ->
    begin match Expr.refine srk expr with
      | `Term t -> 
        let term = Term.eval srk termalg t in
        mk_app srk p [term]
      | _ -> failwith "not in scope of logical fragment"
    end
  | _ -> failwith "not in scope of logical fragment"



let new_to_mfa srk phi =
  let phi = Formula.skolemize_eqpf srk phi in
  let disj bool_list = List.fold_left (||) false bool_list in
  let termalg = function
    | `App (arrsym, [r_term]) -> 
      begin match destruct srk r_term with
        | `Var (ind, `TyInt) -> true, mk_app srk arrsym [mk_var srk ind `TyInt]
        | `App (sym, []) -> false, mk_app srk arrsym [mk_const srk sym]
        | _ -> failwith "not in logical fragment4"
      end
    | `Var (ind, `TyInt) -> true, mk_var srk ind `TyInt
    | `App (sym, []) -> false, mk_const srk sym
    | `Add summands -> 
      let fvs, terms = List.split summands in
      disj fvs, mk_add srk terms
    | `Mul multiplicands -> 
      let fvs, terms = List.split multiplicands in
      disj fvs, mk_mul srk terms
    | `Binop (`Div, (fv1, term1), (fv2, term2)) -> fv1 || fv2, mk_div srk term1 term2
    | `Binop (`Mod, (fv1, term1), (fv2, term2)) -> fv1 || fv2, mk_mod srk term1 term2
    | `Unop (`Floor, (fv, t)) -> fv, mk_floor srk t
    | `Unop (`Neg, (fv, t)) -> fv, mk_neg srk t 
    | `Ite (cond, (fv2, belse), (fv3, bthen)) -> fv2 || fv3, mk_ite srk cond belse bthen
    | _ -> failwith "not in scope of logical fragment3"
  in
  let alg = function
    | `Quantify (`Forall, _, `TyInt, ((qfv, fv), phi)) -> (qfv || fv, fv), phi
    | `Or disjuncts -> 
      let qfv_fvs, _ = List.split disjuncts in
      let qfvs, fvs = List.split qfv_fvs in
      let fresh = mk_symbol srk `TyInt in
      let f ind ((qfv, _), phi) =
        if qfv then  
           mk_and srk [phi; mk_eq srk (mk_const srk fresh) (mk_int srk ind)]
        else phi
      in
      (disj qfvs, disj fvs), mk_or srk (List.mapi f disjuncts)
    | `Tru -> (false, false), mk_true srk
    | `Fls -> (false, false), mk_false srk
    | `Atom (`Eq, x, y) ->
      let fv1, term1 = Term.eval srk termalg x in
      let fv2, term2 = Term.eval srk termalg y in
      (false, fv1 || fv2),  mk_eq srk term1 term2
    | `Atom (`Leq, x, y) ->
      let fv1, term1 = Term.eval srk termalg x in
      let fv2, term2 = Term.eval srk termalg y in
      (false, fv1 || fv2),  mk_leq srk term1 term2
    | `Atom (`Lt, x, y) ->
      let fv1, term1 = Term.eval srk termalg x in
      let fv2, term2 = Term.eval srk termalg y in
      (false, fv1 || fv2),  mk_lt srk term1 term2
    | `And conjuncts ->
      let qfv_fvs, phis = List.split conjuncts in
      let qfvs, fvs = List.split qfv_fvs in
      (disj qfvs, disj fvs), mk_and srk phis
    | `Ite (((false, false), cond), ((qfv2, fv2), bthen), ((qfv3, fv3), belse)) ->
      (qfv2 || qfv3, fv2 || fv3), mk_ite srk cond bthen belse
    | `Not ((false, false), form) -> (false, false), mk_not srk form           
    |`Proposition (`App (p, [expr])) ->
      begin match Expr.refine srk expr with
        | `Term t -> 
          let fv, term = Term.eval srk termalg t in
          (false, fv), mk_app srk p [term]
        | _ -> failwith "not in scope of logical fragment2"
      end
    | _ -> failwith "not in scope of logical fragment1"
  in
  let _, matr = Formula.eval srk alg phi in
  matr


let new_mfa_to_lia srk matrix =
  let const_reads = Hashtbl.create 100 in
  let univ_reads = Hashtbl.create 100 in
  let temp_univ_sym = mk_symbol srk `TyInt in 
  let termalg = function
    | `App (arrsym, [readterm]) ->
      begin match destruct srk readterm with
        | `Var (_, `TyInt) ->
          if not (Hashtbl.mem univ_reads arrsym) then
            Hashtbl.add univ_reads arrsym (Hashtbl.length univ_reads) else ();
          mk_var srk (Hashtbl.find univ_reads arrsym) `TyInt
        | `App (const, []) -> 
          if not (Hashtbl.mem const_reads (arrsym, const)) then
            Hashtbl.add const_reads (arrsym, const) (mk_symbol srk `TyInt) else ();
          mk_const srk (Hashtbl.find const_reads (arrsym, const))
        | _ -> failwith "not flat"
      end
    | `Var (_, `TyInt) -> mk_const srk temp_univ_sym
    | obj ->  dataless_termalg_helper srk obj 
  in
  let matrix = Formula.eval srk (dataless_formalg_helper srk termalg) matrix in
  let subst_for_univ_sym sym = 
    if sym = temp_univ_sym 
    then mk_var srk (Hashtbl.length univ_reads)`TyInt 
    else mk_const srk sym
  in
  let matrix = substitute_const srk subst_for_univ_sym matrix in
  let both_reads = 
    BatHashtbl.filteri 
      (fun (arrsym, _) _ -> Hashtbl.mem univ_reads arrsym) 
      const_reads 
  in
  let add_consistency_clause (arrsym, const) new_const conjuncts =
    let conjunct = 
      mk_if 
        srk 
        (mk_eq srk (mk_var srk (Hashtbl.length univ_reads) `TyInt) (mk_const srk const))
        (mk_eq srk (mk_var srk (Hashtbl.find univ_reads arrsym) `TyInt) (mk_const srk new_const))
    in
    conjunct :: conjuncts
  in
  let consistency_conjs = Hashtbl.fold add_consistency_clause both_reads [] in
  let matrix = mk_and srk (matrix :: consistency_conjs) in
  let phi = 
    Hashtbl.fold 
      (fun _ _ phi -> mk_exists srk ~name:"_" `TyInt phi) 
      univ_reads 
      matrix
  in
  phi
    
module Array_analysis (Iter : PreDomain) = struct

  type 'a t = 'a formula

  let abstract = failwith "todo 4"

  let equal = failwith "todo 5"

  let widen = failwith "todo 6"

  let join = failwith "todo 7"

  let exp =
    (*let qpf, bbu, matr = to_mfa srk phi in
    let arruniv, arrother = get_array_syms srk matr bbu in
    let lia = mfa_to_lia srk (qpf, matr) arruniv arrother bbu in 
    lia*) failwith "todo"

  let pp = failwith "todo 10"

end
