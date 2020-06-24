open Syntax
open Iteration
module V = Linear.QQVector
module M = Linear.QQMatrix
module Z = Linear.ZZVector
module H = Abstract
include Log.Make(struct let name = "srk.array:" end)

type 'a t = 'a formula

(*let projection = failwith "todo 1"*)

let new_to_mfa srk (phi : 'a formula) : 'a formula =
  let skolemtbl = Hashtbl.create 100 in
  let rec skolemize srk args expr =
    let depth = Option.get (List.hd args) in
    let univ_depth = List.nth args 1 in
    match destruct srk expr with
    | `Var (i, `TyInt) ->
      if Option.is_none univ_depth || depth - i < Option.get univ_depth
      then Some (Hashtbl.find skolemtbl (depth - i - 1))
      else Some (mk_var srk i `TyInt)
    | `Quantify (`Forall, name, `TyInt, phi) ->
      Some (mk_forall srk ~name:name `TyInt (custom_eval srk [Some (depth + 1); Some (depth + 1)] skolemize phi))
    | `Quantify (`Exists, _, `TyInt, phi) ->
        Hashtbl.add skolemtbl depth (mk_const srk (mk_symbol srk `TyInt));
        let res = custom_eval srk [Some (depth + 1); univ_depth] skolemize phi in
        Hashtbl.remove skolemtbl depth;
        Some res
    | _ -> None
  in
  let phi = custom_eval srk [Some 0; None] skolemize phi in
  let disj bool_list = List.fold_left (||) false bool_list in
  let alg = function
    | `Quantify (`Forall, _, `TyInt, (false, phi)) -> true, phi
    | `Or disjuncts -> 
      let qfvs, _ = List.split disjuncts in
      let fresh = mk_symbol srk `TyInt in
      let f ind (qfv, phi) =
        if qfv then  
           mk_and srk [phi; mk_eq srk (mk_const srk fresh) (mk_int srk ind)]
        else phi
      in
      disj qfvs, mk_or srk (List.mapi f disjuncts)
    | `Tru -> false, mk_true srk
    | `Fls -> false, mk_false srk
    | `Atom (`Eq, x, y) -> false,  mk_eq srk x y
    | `Atom (`Leq, x, y) -> false,  mk_leq srk x y
    | `Atom (`Lt, x, y) -> false,  mk_lt srk x y
    | `And conjuncts ->
      let qfvs, phis = List.split conjuncts in
      disj qfvs, mk_and srk phis
    | `Ite ((false, cond), (qfv2, bthen), (qfv3, belse)) -> qfv2 || qfv3, mk_ite srk cond bthen belse
    | `Not (false, phi) -> false, mk_not srk phi          
    |`Proposition (`App (p, [expr])) ->
      begin match Expr.refine srk expr with
        | `Term t -> false, mk_app srk p [t]
        | _ -> failwith "not in scope of logical fragment"
      end
    | _ -> failwith "not in scope of logical fragment"
  in
  let _, matr = Formula.eval srk alg phi in
  let matr = (matr :> 'a formula) in
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
    | open_term -> Term.construct srk open_term 
  in
  let formalg = function
    | `Atom (`Eq, x, y) -> mk_eq srk (Term.eval srk termalg x) (Term.eval srk termalg y)
    | `Atom (`Leq, x, y) -> mk_leq srk (Term.eval srk termalg x) (Term.eval srk termalg y)
    | `Atom (`Lt, x, y) -> mk_lt srk (Term.eval srk termalg x) (Term.eval srk termalg y)
    | `Proposition (`App (p, [expr])) ->
      begin match Expr.refine srk expr with
        | `Term t -> 
          let term = Term.eval srk termalg t in
          mk_app srk p [term]
        | _ -> failwith "not in scope of logical fragment"
      end
    | open_formula -> Formula.construct srk open_formula
  in
  let matrix : 'a formula = Formula.eval srk formalg matrix in
  let uquant_depth = Hashtbl.length univ_reads in
  let subst_for_univ_sym sym = 
    if sym = temp_univ_sym 
    then mk_var srk uquant_depth `TyInt 
    else mk_const srk sym
  in
  let matrix = substitute_const srk subst_for_univ_sym matrix in
  let both_reads = 
    BatHashtbl.filteri 
      (fun (arrsym, _) _ -> Hashtbl.mem univ_reads arrsym) 
      const_reads 
  in
  let add_consistency_clause (arrsym, readsym) new_sym conjuncts =
    let conjunct = 
      mk_if 
        srk 
        (mk_eq srk (mk_var srk uquant_depth `TyInt) (mk_const srk readsym))
        (mk_eq srk (mk_var srk (Hashtbl.find univ_reads arrsym) `TyInt) (mk_const srk new_sym))
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
