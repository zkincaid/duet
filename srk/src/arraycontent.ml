open Syntax
open Iteration
module V = Linear.QQVector
module M = Linear.QQMatrix
module Z = Linear.ZZVector
module H = Abstract
include Log.Make(struct let name = "srk.array:" end)

type 'a t = 'a formula

(*let projection = failwith "todo 1"*)

let data_termalg_helper srk empty_case merge obj =
  match obj with
  | `Real qq -> empty_case, mk_real srk qq
  | `Add sum -> 
    let analy_objs, terms = List.split sum in
    merge analy_objs, mk_add srk terms
  | `Mul product -> 
    let analy_objs, terms = List.split product in
    merge analy_objs, mk_mul srk terms
  | `Binop (`Div, (analy_obj1, term1), (analy_obj2, term2)) -> 
    merge [analy_obj1; analy_obj2], mk_div srk term1 term2
  | `Binop (`Mod, (analy_obj1, term1), (analy_obj2, term2)) -> 
    merge [analy_obj1; analy_obj2], mk_mod srk term1 term2
  | `Unop (`Floor, (analy_obj, t)) -> analy_obj, mk_floor srk t
  | `Unop (`Neg, (analy_obj, t)) -> analy_obj, mk_neg srk t 
  | `Ite (_, _, _) -> failwith "TOOD"
  | _ -> failwith "not in scope of logical fragment"

let data_formalg_helper srk empty_case merge termalg obj =
  match obj with
  | `Tru -> empty_case, mk_true srk
  | `Fls -> empty_case, mk_false srk
  | `Atom (`Eq, x, y) ->
    let analy_obj1, term1 = Term.eval srk termalg x in
    let analy_obj2, term2 = Term.eval srk termalg y in
    merge [analy_obj1; analy_obj2], mk_eq srk term1 term2
  | `Atom (`Leq, x, y) ->
    let analy_obj1, term1 = Term.eval srk termalg x in
    let analy_obj2, term2 = Term.eval srk termalg y in
    merge [analy_obj1; analy_obj2], mk_leq srk term1 term2
  | `Atom (`Lt, x, y) ->
    let analy_obj1, term1 = Term.eval srk termalg x in
    let analy_obj2, term2 = Term.eval srk termalg y in
    merge [analy_obj1; analy_obj2], mk_lt srk term1 term2
  | `And cons ->
    let analy_objs, forms = List.split cons in
    merge analy_objs, mk_and srk forms
  | `Or disj -> 
    let analy_objs, forms = List.split disj in
    merge analy_objs, mk_or srk forms
  | `Ite ((analy_obj1, cond), (analy_obj2, bthen), (analy_obj3, belse)) ->
    merge [analy_obj1; analy_obj2; analy_obj3], mk_ite srk cond bthen belse
  | `Not (analy_obj, form) -> analy_obj, mk_not srk form           
  |`Proposition (`App (p, [expr])) ->
    begin match Expr.refine srk expr with
      | `Term t -> 
        let analy_obj, term = Term.eval srk termalg t in
        analy_obj, mk_app srk p [term]
      | _ -> failwith "not in scope of logical fragment"
    end
  | _ -> failwith "not in scope of logical fragment"

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
  let sub_tbl = Hashtbl.create 10 in
  let univequivclass = ref None in
  let empty_case = false, (0, Hashtbl.create 0) in
  let var_case ind sym =
    Hashtbl.add sub_tbl sym (BatUref.uref sym);
    let tbl = Hashtbl.create 1 in
    Hashtbl.add tbl ind sym;
    (false, (0, tbl))
  in
  let merge objs =
    let bools, offset_tbls = List.split objs in
    let merge_two (off0, tbl0) (off, tbl) =
      let frm_off, frm_tbl, to_off, to_tbl =
        if Hashtbl.length tbl0 > Hashtbl.length tbl then off, tbl, off0, tbl0
        else off0, tbl0, off, tbl
      in
      let unify frm_ind frm_sym =
        match Hashtbl.find_opt to_tbl (to_off + frm_ind - frm_off) with 
        | Some to_sym -> BatUref.unite 
                           (Hashtbl.find sub_tbl to_sym) 
                           (Hashtbl.find sub_tbl frm_sym)
        | None -> Hashtbl.add to_tbl (to_off + frm_ind - frm_off) frm_sym 
      in
      Hashtbl.iter unify frm_tbl;
      to_off, to_tbl
    in
    List.fold_left (||) false bools, List.fold_left merge_two (snd empty_case) offset_tbls
  in
  let rec termalg = function
    | `App (arrsym, [r_term]) -> 
      begin match destruct srk r_term with
        | `Var (ind, `TyInt) ->
          let fresh = mk_symbol srk `TyInt in
          var_case ind fresh, mk_app srk arrsym [mk_const srk fresh]
        | `App (sym, []) -> empty_case, mk_app srk arrsym [mk_const srk sym]
        | _ -> failwith "not in logical fragment"
      end
    | `Var (ind, `TyInt) -> 
      let fresh = mk_symbol srk `TyInt in
      var_case ind fresh, mk_const srk fresh
    | obj -> data_termalg_helper srk empty_case merge obj 
 and alg = function
    | `Quantify (`Exists, _, `TyInt, ((form_has_univ,(offset, tbl)), phi)) ->
      Hashtbl.remove tbl offset;
      (form_has_univ, (offset+1, tbl)), phi
    | `Quantify (`Forall, _, `TyInt, ((false, (offset, tbl)), phi)) ->
      if !univequivclass = None && Hashtbl.mem tbl offset then
        univequivclass := Some (Hashtbl.find sub_tbl (Hashtbl.find tbl offset))
      else ();
      let form_has_univ = if Hashtbl.mem tbl offset then true else false in
      Hashtbl.remove tbl offset;
      (form_has_univ, (offset+1, tbl)), phi
    | `Or disj -> 
      let fresh = mk_symbol srk `TyInt in
      let f ind ((has_univ, offset_tbl), subform) =
        if has_univ then 
          ((has_univ, offset_tbl), 
           mk_and srk [subform; mk_eq srk (mk_const srk fresh) (mk_int srk ind)])
        else ((has_univ, offset_tbl), subform)
      in
      let disj = List.mapi f disj in
      let analy_objs, forms = List.split disj in
      merge analy_objs, mk_or srk forms
    | obj -> data_formalg_helper srk empty_case merge termalg obj
  in
  let _, matr = Formula.eval srk alg phi in
  let sub_map sym =
    match Hashtbl.find_opt sub_tbl sym with
    | Some uref -> 
      if Option.is_none !univequivclass || 
         not (BatUref.equal (Option.get !univequivclass) uref)
      then 
        mk_const srk (BatUref.uget uref)
      else mk_var srk 0 `TyInt
    | None -> mk_const srk sym
  in
  let matr = substitute_const srk sub_map matr in
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
