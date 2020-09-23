(* Constrainted horn clauses *)
open Syntax

type 'a chccontext = 
  { srk : 'a context;  relations : (string * typ list) BatDynArray.t}
type relation = string [@@deriving ord]
type relation_atom = relation * symbol list
type 'a hypothesis = relation_atom list * 'a formula
type conclusion = relation_atom
type 'a rule = 'a hypothesis * conclusion
type 'a query = relation
type 'a chc = {rules : 'a rule list; queries : 'a query list}

module Relation = struct
  type t = relation [@@deriving ord]
end

module RSet = BatSet.Make(Relation)


let rel_sym_of (relation, _) = relation
let params_of (_, params) = params



let show_rel rel = "R_"^(rel)
let show_rel_atom srk (rel, symbols) =
  let show_symbol srk sym = 
    (show_symbol srk sym)^":"^(string_of_int (int_of_symbol sym)) 
  in
  let inner_paren = if BatList.is_empty symbols then ""
    else (
      List.fold_left 
        (fun str symbol -> str^", "^(show_symbol srk symbol)) 
        (show_symbol srk (List.hd symbols)) 
        (List.tl symbols))
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

let typ_of_sort sort =
  let open Z3enums in
  match Z3.Sort.get_sort_kind sort with
  | REAL_SORT -> `TyReal
  | INT_SORT -> `TyInt
  | BOOL_SORT -> `TyBool
  | _ -> failwith "TODO: allow function types"

let rl_atom_of_z3prd srk ?(ind_to_sym=BatHashtbl.create 100) names z3prd =
  let decl = Z3.Expr.get_func_decl z3prd in
  let rel = Z3.Symbol.to_string (Z3.FuncDecl.get_name decl) in
  let args = List.map 
      (fun arg -> 
         let index = Z3.Quantifier.get_index arg in
         if BatHashtbl.mem ind_to_sym index then
           BatHashtbl.find ind_to_sym index
         else (
           let sort = typ_of_sort (Z3.Expr.get_sort arg) in
           let sym = 
             mk_symbol srk ~name:(Z3.Symbol.to_string names.(index)) sort 
           in
           BatHashtbl.add ind_to_sym index sym;
           sym)) 
      (Z3.Expr.get_args z3prd) in
  rel, args

let rl_atom_of_z3prd_fresh srk ?(ind_to_sym=BatHashtbl.create 100) names z3prd =
  let fresh_index_map = BatHashtbl.create 100 in
  let eq_syms = ref [] in
  let atom = rl_atom_of_z3prd srk ~ind_to_sym:fresh_index_map names z3prd in
  BatHashtbl.iter (fun ind sym ->
      if BatHashtbl.mem ind_to_sym ind 
      then eq_syms := ((BatHashtbl.find ind_to_sym ind), sym) :: !eq_syms
      else BatHashtbl.add ind_to_sym ind sym)
    fresh_index_map;
  atom, !eq_syms

let parse_file ?(context=Z3.mk_context []) srk filename =
  let z3 = context in
  let fp = Z3.Fixedpoint.mk_fixedpoint z3 in
  let z3queries = Z3.Fixedpoint.parse_file fp filename in
  let is_rel_atom z3expr = 
    Z3.FuncDecl.get_decl_kind (Z3.Expr.get_func_decl z3expr) = OP_UNINTERPRETED
  in
  let parse_rule rule =
    let names, matrix =
      if Z3.AST.is_quantifier (Z3.Expr.ast_of_expr rule) then
        let q = Z3.Quantifier.quantifier_of_expr rule in
        BatArray.of_list (Z3.Quantifier.get_bound_variable_names q), 
        Z3.Quantifier.get_body q
      else BatArray.init 0 (fun _ -> failwith "empty array"), rule
    in
    (* Note that we don't substitute phi with ind_to_sym in this function *)
    let parse_hypothesis ?(ind_to_sym=BatHashtbl.create 100) expr = 
      let decl =  Z3.FuncDecl.get_decl_kind (Z3.Expr.get_func_decl expr) in
      begin match decl with
        | OP_AND ->
          let (rels, phis) = 
            List.partition (is_rel_atom) (Z3.Expr.get_args expr) 
          in
          let rel_atoms = 
            List.map (rl_atom_of_z3prd ~ind_to_sym srk names) rels
          in
          let phis = List.map (SrkZ3.formula_of_z3 srk) phis in
          rel_atoms, (mk_and srk phis)
        | OP_UNINTERPRETED -> [rl_atom_of_z3prd srk names expr], mk_true srk
        | OP_OR -> failwith "TODO: OR Case"
        | _ -> [], SrkZ3.formula_of_z3 srk expr
      end
    in
    let decl =  Z3.FuncDecl.get_decl_kind (Z3.Expr.get_func_decl matrix) in
    let args = Z3.Expr.get_args matrix in
    begin match decl, args with
      | (OP_IMPLIES, [hypo;conc]) ->
        let ind_to_sym = BatHashtbl.create 100 in
        let (atoms, phi) = parse_hypothesis ~ind_to_sym hypo in
        let conc, eq_syms = rl_atom_of_z3prd_fresh srk ~ind_to_sym names conc in
        let phi = mk_and 
            srk 
            ((substitute 
               srk 
               (fun ind -> 
                  if BatHashtbl.mem ind_to_sym ind 
                  then mk_const srk (BatHashtbl.find ind_to_sym ind)
                  else failwith "Free var in rule formula not bound in rel")
               phi)
             :: (List.map 
                   (fun (sym1, sym2) -> mk_eq_syms srk sym1 sym2) 
                   eq_syms))
        in
        (atoms, phi), conc
      | (OP_UNINTERPRETED, _) ->
        let hypo = [], mk_true srk in
        let conc = rl_atom_of_z3prd srk names matrix in
        hypo, conc
      | _ -> failwith "Rule not well formed"
    end
  in
  let parse_query query =
    Z3.Symbol.to_string (Z3.FuncDecl.get_name (Z3.Expr.get_func_decl query))
  in
  let rules = List.map parse_rule (Z3.Fixedpoint.get_rules fp) in
  let queries = List.map parse_query z3queries in
  {rules; queries}


let get_rel_syms chc =
  let rset = 
    List.fold_left 
      (fun rset ((rel_atom_lst, _), conc) ->
         List.fold_left 
           (fun rset rel_atom -> RSet.add (rel_sym_of rel_atom) rset)
           (RSet.add (rel_sym_of conc) rset)
           rel_atom_lst)
      (RSet.of_list chc.queries)
      chc.rules
  in
  rset

let to_weighted_graph srk chc pd =
  let open WeightedGraph in
  let emptyarr = BatArray.init 0 (fun _ -> failwith "empty") in
  let alg = 
    let map_union m1 m2 = Symbol.Map.fold Symbol.Map.add m1 m2 in
    let mk_subst_map a b =
      BatArray.fold_lefti 
        (fun map ind asym -> Symbol.Map.add asym (mk_const srk (b.(ind))) map)
        Symbol.Map.empty
        a
    in
    let is_one (_, _, phi) = Formula.equal phi (mk_true srk) in
    let is_zero (_, _, phi) = Formula.equal phi (mk_false srk) in
    let zero = emptyarr, emptyarr, mk_false srk in
    let one = emptyarr, emptyarr, mk_true srk in
    let add x y =
      if is_zero x then y else if is_zero y then x
      else if is_one x || is_one y then one
      else (
        let (pre, post, _) = x in
        let pre' = Array.map (fun sym -> dup_symbol srk sym) pre in
        let post' = Array.map (fun sym -> dup_symbol srk sym) post in
        let subst (pre, post, phi) = 
          substitute_map
            srk 
            (map_union (mk_subst_map pre pre') (mk_subst_map post post'))
            phi
        in
        pre', post', mk_or srk [subst x; subst y])
    in
    let mul x y = 
      if is_zero x || is_zero y then zero
      else if is_one x then y else if is_one y then x
      else (
        let (pre1, post1, phi1) = x in
        let (pre2, post2, phi2) = y in
        let pre' = Array.map (fun sym -> dup_symbol srk sym) pre1 in
        let post' = Array.map (fun sym -> dup_symbol srk sym) post2 in 
        let rhs_subst = 
          map_union (mk_subst_map post2 post') (mk_subst_map pre2 post1) 
        in
        let phi2 = substitute_map srk rhs_subst phi2 in
        let phi1 = substitute_map srk (mk_subst_map pre1 pre') phi1 in
        let phi' = 
          Quantifier.mbp 
            srk
            (fun sym -> not (Array.mem sym post1))
            (mk_and srk [phi1; phi2])
        in (* quantifiers are not allowed here... why? *)
        pre', post', phi'
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
  let goal_vert = 1 in
  let wg = WeightedGraph.add_vertex (WeightedGraph.empty alg) true_vert in
  let wg = WeightedGraph.add_vertex wg goal_vert in
  let vertexcounter = ref 2 in
  let wg = RSet.fold 
      (fun rel_sym wg -> 
         Hashtbl.add vertex_tbl rel_sym !vertexcounter;
         vertexcounter := !vertexcounter + 1;
         WeightedGraph.add_vertex wg (!vertexcounter - 1))
      (get_rel_syms chc)
      wg
  in
  let wg = 
    List.fold_left
      (fun wg ((rel_atoms, phi), conc) ->
         match rel_atoms with
         | [] -> WeightedGraph.add_edge 
                   wg 
                   true_vert
                   (emptyarr, BatArray.of_list (params_of conc), phi)
                   (Hashtbl.find vertex_tbl (rel_sym_of conc))
         | [hd] ->
           WeightedGraph.add_edge 
             wg 
             (Hashtbl.find vertex_tbl (rel_sym_of hd))
             (BatArray.of_list (params_of hd), 
              BatArray.of_list (params_of conc), 
              phi)
             (Hashtbl.find vertex_tbl (rel_sym_of conc))
         | _ -> failwith "Rule with multiple relations in hypothesis")
      wg
      chc.rules
  in
  let wg =
    List.fold_left
      (fun wg rel -> 
         WeightedGraph.add_edge
           wg
           (Hashtbl.find vertex_tbl rel)
           alg.one
           goal_vert)
      wg
      chc.queries
  in
  wg, true_vert, goal_vert
