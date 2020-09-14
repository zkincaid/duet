(* Constrainted horn clauses *)
open Syntax

type 'a chccontext = 
  { srk : 'a context;  relations : (string * typ list) BatDynArray.t}
type relation = string
type 'a relation_atom = relation * 'a term list
type 'a hypothesis = 'a relation_atom list * 'a formula
type 'a conclusion = 'a relation_atom
type 'a clause = 'a hypothesis * 'a conclusion
type 'a chc = 'a clause list (*TODO: add queries*)

let show_rel rel = "R_"^(rel)
let show_rel_atom srk (rel, terms) = 
  let inner_paren = if BatList.is_empty terms then ""
    else (
      List.fold_left 
        (fun str term -> str^", "^(Term.show srk term)) 
        (Term.show srk (List.hd terms)) 
        (List.tl terms))
  in
  (show_rel rel)^"("^inner_paren^")"

let show_hypothesis srk (rel_atoms, phi) =
  (List.fold_left 
     (fun str rel_atom -> (show_rel_atom srk rel_atom)^"/\\"^str) 
     "" 
     rel_atoms)
  ^(Formula.show srk phi)

let show_conclusion = show_rel_atom

let show_clause srk (hypo,conc) = 
  (show_hypothesis srk hypo)^"=>"^(show_conclusion srk conc)

let show_chc srk chc =
  List.fold_left (fun str rule -> str^"\n"^(show_clause srk rule)) "" chc

let rl_atom_of_z3pred srk z3pred =
  let decl = Z3.Expr.get_func_decl z3pred in
  let rel = Z3.Symbol.to_string (Z3.FuncDecl.get_name decl) in
  let args = List.map (fun arg -> SrkZ3.term_of_z3 srk arg) (Z3.Expr.get_args z3pred) in
  rel, args

let parse_file ?(context=Z3.mk_context []) srk filename =
  let z3 = context in
  let fp = Z3.Fixedpoint.mk_fixedpoint z3 in
  let _ = Z3.Fixedpoint.parse_file fp filename in
  let is_rel_atom z3expr = 
    let decl = Z3.Expr.get_func_decl z3expr in
    Z3.FuncDecl.get_decl_kind decl = OP_UNINTERPRETED
  in
  let parse_hypothesis expr = 
    let decl =  Z3.FuncDecl.get_decl_kind (Z3.Expr.get_func_decl expr) in
    begin match decl with
      | OP_AND ->
        let (rels, phis) = List.partition (is_rel_atom) (Z3.Expr.get_args expr) in
        let rel_atoms = List.map (rl_atom_of_z3pred srk) rels in
        let phis = List.map (SrkZ3.formula_of_z3 srk) phis in
        rel_atoms, (mk_and srk phis)
      | OP_UNINTERPRETED -> [rl_atom_of_z3pred srk expr], mk_true srk
      | OP_OR -> failwith "TODO"
      | _ -> [], SrkZ3.formula_of_z3 srk expr
    end
  in
  let parse_rule rule = 
    let matrix =
      if Z3.AST.is_quantifier (Z3.Expr.ast_of_expr rule) then
        Z3.Quantifier.get_body (Z3.Quantifier.quantifier_of_expr rule)
      else rule
    in
    let decl =  Z3.FuncDecl.get_decl_kind (Z3.Expr.get_func_decl matrix) in
    let args = Z3.Expr.get_args matrix in
    begin match decl, args with
      | (OP_IMPLIES, [hypo;conc]) ->
        let hypo = parse_hypothesis hypo in
        let conc = rl_atom_of_z3pred srk conc in
        hypo, conc
      | (OP_UNINTERPRETED, _) ->
        let hypo = [], mk_true srk in
        let conc = rl_atom_of_z3pred srk matrix in
        hypo, conc
      | _ -> failwith "Rule not well formed"
    end
  in
  List.map parse_rule (Z3.Fixedpoint.get_rules fp)
