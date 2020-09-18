(* Constrainted horn clauses *)
open Syntax
open Iteration

type 'a chccontext = 
  { srk : 'a context;  relations : (string * typ list) BatDynArray.t}
type relation = string [@@deriving ord]
type relation_atom = relation * symbol list
type 'a hypothesis = relation_atom list * 'a formula
type conclusion = relation_atom
type 'a rule = 'a hypothesis * conclusion
type 'a query = 'a hypothesis
type 'a chc = {rules : 'a rule list; queries : 'a query list}

module Relation = struct
  type t = relation [@@deriving ord]
end

module RSet = BatSet.Make(Relation)


let rel_sym_of (relation, _) = relation
(* TODO: change params from expr list to sym list *)
let params_of (_, params) = params



let show_rel rel = "R_"^(rel)
let show_rel_atom srk (rel, terms) = 
  let inner_paren = if BatList.is_empty terms then ""
    else (
      List.fold_left 
        (fun str term -> str^", "^(show_symbol srk term)) 
        (show_symbol srk (List.hd terms)) 
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

let show_rule srk (hypo,conc) = 
  (show_hypothesis srk hypo)^"=>"^(show_conclusion srk conc)

let show_chc srk chc =
  List.fold_left (fun str rule -> str^"\n"^(show_rule srk rule)) "" chc.rules

let rl_atom_of_z3pred srk z3pred : relation_atom =
  let decl = Z3.Expr.get_func_decl z3pred in
  let rel = Z3.Symbol.to_string (Z3.FuncDecl.get_name decl) in
  let args = List.map (fun arg -> SrkZ3.term_of_z3 srk arg) (Z3.Expr.get_args z3pred) in
  let fresh_syms = List.map (fun arg -> mk_symbol srk (term_typ srk arg)) args in
  rel, fresh_syms

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
  let rules = List.map parse_rule (Z3.Fixedpoint.get_rules fp) in
  {rules=rules; queries=[]}
  (* TODO: queries *)


module LinCHC = struct
  open WeightedGraph
  type 'a linhypo = relation_atom option * 'a formula
  type 'a linrule = 'a linhypo * conclusion
  type 'a linquery = 'a linhypo
  type 'a linchc = {rules : 'a linrule list; queries : 'a linquery list}

  let get_rel_syms linchc =
    let add_hypo_opt rset rel_atom_opt =
      match rel_atom_opt with
      | None -> rset
      | Some v -> RSet.add (rel_sym_of v) rset
    in
    let rset = 
      List.fold_left 
        (fun rset ((rel_atom_opt, _), conc) ->
          let rset = RSet.add (rel_sym_of conc) rset in
          add_hypo_opt rset rel_atom_opt)
        RSet.empty
        linchc.rules
    in
    List.fold_left 
      (fun rset (rel_atom_opt, _) -> add_hypo_opt rset rel_atom_opt)
      rset
      linchc.queries

  let to_weighted_graph srk linchc pd =
    let emptyarr = BatArray.init 0 (fun f -> failwith "empty") in
    let alg = 
      let mk_subst_map a b =
        BatArray.fold_lefti 
          (fun map ind asym -> Symbol.Map.add asym (mk_const srk (b.(ind))) map)
          Symbol.Map.empty
          a
      in
      let is_one (pre, post, phi) = Formula.equal phi (mk_true srk) in
      let is_zero (pre, post, phi) = Formula.equal phi (mk_false srk) in
      let zero = emptyarr, emptyarr, mk_false srk in
      let one = emptyarr, emptyarr, mk_true srk in
      let add x y =
        if is_zero x then y else if is_zero y then x
        else if is_one x || is_one y then one
        else (
          let (pre1, post1, phi1) = x in
          let (pre2, post2, phi2) = y in
          let subst_map_pre = mk_subst_map pre2 pre1 in
          let subst_map_post = mk_subst_map post2 post1 in
          let rhs_map = Symbol.Map.union subst_map_pre subst_map_post in
          pre1, post1, mk_or srk [phi1; (substitute_map srk rhs_map phi2)]
        )
      in
      let mul x y =
        if is_zero x || is_zero y then zero
        else if is_one x then y else if is_one y then x
        else (
          let (pre1, post1, phi1) = x in
          let (pre2, post2, phi2) = y in
          let subst_map = mk_subst_map pre2 post1 in
          pre1, post2, mk_and srk [phi1; (substitute_map srk subst_map phi2)] 
        )
      in
      let star (pre, post, phi) =
        let module PD = (val pd : Iteration.PreDomain) in
        let trs =
          BatArray.fold_lefti
            (fun trs ind presym -> (presym, post.(ind)) :: trs)
            []
            pre
        in
        let lc = mk_symbol srk `TyInt in
        let tr_phi = TransitionFormula.make phi trs in
        pre, post, 
        PD.exp srk trs (mk_const srk lc) (PD.abstract srk tr_phi)
      in
      {mul; add; star; zero; one}
    in
    let vertex_tbl = Hashtbl.create 100 in
    let true_vert = 0 in
    let false_vert = 1 in
    let wg = WeightedGraph.add_vertex (WeightedGraph.empty alg) true_vert in
    let wg = WeightedGrapg.add_vertex wg false_vert in
    let vertexcounter = ref 2 in
    let wg = List.fold_left 
        (fun wg rel_sym -> 
           Hashtbl.add vertex_tbl rel_sym vertexcounter;
           vertexcounter := !vertexcounter + 1;
           WeightedGraph.add_vertex wg (!vertexcounter - 1))
        wg
        (get_rel_syms chc)
    in
    List.fold_left
      (fun wg ((rel_atom_opt, phi), conc) ->
         match rel_atom_opt with
         | None -> WeightedGraph.add_edge 
                     wg 
                     true_vert
                     (emptyarr, params_of conc, phi)
                     (Hashtbl.find vertex_tbl (rel_sym_of conc))
         | Some hypo_atom ->
           WeightedGraph.add_edge 
             wg 
             (Hashtbl.find vertex_tbl (rel_sym_of hypo_atom))
             (BatArray.of_list (params_of hypo_atom), 
              BatArray.of_list (params_of conc), 
              phi)
             (Hashtbl.find vertex_tbl (rel_sym_of conc)))
      wg
      linchc.rules
      (* TODO: Queries *)



end
