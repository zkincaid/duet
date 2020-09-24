(* Constrainted horn clauses *)
open Syntax
module DynArray = BatDynArray

type relation = int
type 'b relcontext = (string * typ list) DynArray.t
type ('a, 'b) relation_atom = relation * symbol list
type ('a, 'b) hypothesis = ('a, 'b) relation_atom list * 'a formula
type ('a, 'b) rule = ('a, 'b) hypothesis * ('a, 'b) relation_atom
type ('a, 'b) query = relation
type 'c rule_name = int
type 'c query_name = int
type ('a, 'b, 'c) chc = 
  {rules : ('c rule_name, ('a, 'b) rule)  Hashtbl.t;
   rule_counter : int ref;
   queries : ('c query_name, ('a, 'b) query)  Hashtbl.t;
   query_counter : int ref}

let mk_relcontext = DynArray.create ()

module Relation = struct
  type t = relation 
  module Set = SrkUtil.Int.Set 
  let compare = Stdlib.compare
  let mk_relation rel_ctx ?(name="R") typ =
      DynArray.add rel_ctx (name, typ);
      DynArray.length rel_ctx - 1

  let type_of rel_ctx rel = snd (DynArray.get rel_ctx rel)
  let name_of rel_ctx rel = fst (DynArray.get rel_ctx rel)
  let pp rel_ctx formatter rel =
    Format.fprintf formatter "@%s:R%n@" (name_of rel_ctx rel) rel
  let show rel_ctx = SrkUtil.mk_show (pp rel_ctx)
end

let rel_sym_of (relation, _) = relation
let params_of (_, params) = params

let pp_relation_atom srk rel_ctx formatter (rel, symbols) =
    Format.fprintf formatter "%a(@[%a@])"
      (Relation.pp rel_ctx) rel
      (SrkUtil.pp_print_enum_nobox (pp_symbol srk)) (BatList.enum symbols)
let pp_hypothesis srk rel_ctx formatter (rel_atoms, phi) =
  Format.fprintf formatter "(@[";
  SrkUtil.pp_print_enum
    ~pp_sep:(fun formatter () -> Format.fprintf formatter "@ /\\ ")
    (pp_relation_atom srk rel_ctx)
    formatter
    (BatList.enum rel_atoms);
  Format.fprintf formatter "@]/\\%a)" (Formula.pp srk) phi
let pp_rule srk rel_ctx formatter (hypo, conc) =
  Format.fprintf formatter "(@[%a@ => %a@])"
    (pp_hypothesis srk rel_ctx) hypo
    (pp_relation_atom srk rel_ctx) conc
let pp_query _ = Relation.pp

let show_relation_atom srk rel_ctx = 
  SrkUtil.mk_show (pp_relation_atom srk rel_ctx)
let show_hypothesis srk rel_ctx = SrkUtil.mk_show (pp_hypothesis srk rel_ctx)
let show_rule srk rel_ctx = SrkUtil.mk_show (pp_rule srk rel_ctx)
let show_query srk rel_ctx = SrkUtil.mk_show (pp_query srk rel_ctx)

module Chc = struct
  type ('a, 'b, 'c) t = ('a, 'b, 'c) chc 

  let pp srk rel_ctx formatter chc = 
    Format.fprintf formatter "(Rules:\n@[";
    SrkUtil.pp_print_enum
      ~pp_sep:(fun formatter () -> Format.fprintf formatter "@ \n ")
      (pp_rule srk rel_ctx)
      formatter
      (BatHashtbl.values chc.rules);
    Format.fprintf formatter "@]\nQueries:@[%a@])"
    (SrkUtil.pp_print_enum_nobox (Relation.pp rel_ctx)) 
      (BatHashtbl.values chc.queries)


  let show srk rel_ctx = SrkUtil.mk_show (pp srk rel_ctx)

  let create ?(rlength=97) ?(qlength=97) () =
    let rules = Hashtbl.create rlength in
    let queries = Hashtbl.create qlength in
    let rule_counter = ref 0 in
    let query_counter = ref 0 in
    {rules;rule_counter;queries;query_counter}

  let copy chc = 
    {rules=Hashtbl.copy chc.rules;
     rule_counter = ref !(chc.rule_counter);
     queries=Hashtbl.copy chc.queries;
     query_counter = ref !(chc.query_counter)}

  let add tbl counter obj =
    Hashtbl.add tbl !counter obj;
    counter := !(counter) + 1;
    !(counter) - 1

  let add_rule chc rule = add chc.rules chc.rule_counter rule
  let add_query chc query = add chc.queries chc.query_counter query


  let del tbl name =
    if Hashtbl.mem tbl name then (
      BatHashtbl.remove_all tbl name;
      true)
    else false

  let del_rule chc rule_name = del chc.rules rule_name
  let del_query chc query_name = del chc.queries query_name

  let upd tbl name obj =
    Hashtbl.add tbl name obj

  let upd_rule chc rule_name rule = upd chc.rules rule_name rule
  let upd_query chc query_name query = upd chc.queries query_name query

  let get_rules chc = chc.rules
  let get_queries chc = chc.queries
  let get_rule chc rule_name = Hashtbl.find chc.rules rule_name
  let get_query chc query_name = Hashtbl.find chc.queries query_name

  let get_relations_used chc =
    Hashtbl.fold
      (fun _ ((hypo_atoms, _), conc_atom) rset ->
         List.fold_left
           (fun rset rel_atom -> Relation.Set.add (rel_sym_of rel_atom) rset)
           (Relation.Set.add (rel_sym_of conc_atom) rset)
           hypo_atoms)
      chc.rules
      (Hashtbl.fold 
         (fun _ query rset -> Relation.Set.add query rset)
         chc.queries
         Relation.Set.empty)

  let is_linear chc =
    BatHashtbl.fold 
      (fun _ ((rel_atoms, _), _) acc -> acc && (List.length rel_atoms) <= 1)
      chc.rules
      true


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
          in
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
    let true_vert = -1 in
    let goal_vert = 2 in
    let wg = WeightedGraph.add_vertex (WeightedGraph.empty alg) true_vert in
    let wg = WeightedGraph.add_vertex wg goal_vert in
    let vertexcounter = ref 0 in
    let wg = Relation.Set.fold 
        (fun rel_sym wg -> 
           Hashtbl.add vertex_tbl rel_sym !vertexcounter;
           vertexcounter := !vertexcounter + 1;
           WeightedGraph.add_vertex wg (!vertexcounter - 1))
        (get_relations_used chc)
        wg
    in
    let wg = 
      Hashtbl.fold
        (fun _ ((rel_atoms, phi), conc) wg ->
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
        chc.rules
        wg
    in
    let wg =
      Hashtbl.fold
        (fun _ rel wg -> 
           WeightedGraph.add_edge
             wg
             (Hashtbl.find vertex_tbl rel)
             alg.one
             goal_vert)
        chc.queries
        wg
    in
    wg, true_vert, goal_vert

  let has_reachable_goal srk chc pd = 
    if is_linear chc then (
      let wg, true_vert, goal_vert = to_weighted_graph srk chc pd in
      let _, _, phi = WeightedGraph.path_weight wg true_vert goal_vert in
      let solver = Smt.mk_solver srk in
      Smt.Solver.add solver [phi];
      begin match Smt.Solver.get_model solver with
        | `Unsat -> `No
        | `Unknown -> `Unknown
        | `Sat _ -> `Yes
      end)
    else failwith "No methods for solving non lin chc"


end

module ChcSrkZ3 = struct
  
  let typ_of_sort sort =
    let open Z3enums in
    match Z3.Sort.get_sort_kind sort with
    | REAL_SORT -> `TyReal
    | INT_SORT -> `TyInt
    | BOOL_SORT -> `TyBool
    | _ -> failwith "TODO: allow function types"

  let rel_atom_of_z3 srk rel_ctx ind_to_sym rsym_to_int names z3pred =
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
        (Z3.Expr.get_args z3pred) in
    let decl = Z3.Expr.get_func_decl z3pred in
    let rsym = Z3.Symbol.to_string (Z3.FuncDecl.get_name decl) in
    let relation = 
      if Hashtbl.mem rsym_to_int rsym then Hashtbl.find rsym_to_int rsym
      else (
        let typ = List.map (fun arg -> typ_symbol srk arg) args in
        let res = Relation.mk_relation rel_ctx ~name:rsym typ in
        Hashtbl.add rsym_to_int rsym res;
        res)
    in
    relation, args

  let rel_atom_of_z3_fresh srk rel_ctx ind_to_sym rsym_to_int names z3pred =
    let fresh_index_map = BatHashtbl.create 91 in
    let eq_syms = ref [] in
    let atom = 
      rel_atom_of_z3 srk rel_ctx fresh_index_map rsym_to_int names z3pred 
    in
    BatHashtbl.iter (fun ind sym ->
        if BatHashtbl.mem ind_to_sym ind 
        then eq_syms := ((BatHashtbl.find ind_to_sym ind), sym) :: !eq_syms
        else BatHashtbl.add ind_to_sym ind sym)
      fresh_index_map;
    atom, !eq_syms


  let parse_z3fp ?(z3queries=[]) srk rel_ctx z3fp =
    let rsym_to_int = BatHashtbl.create 91 in
    let decl_kind e = Z3.FuncDecl.get_decl_kind (Z3.Expr.get_func_decl e) in
    let parse_rule rule =
      let names, matrix =
        if Z3.AST.is_quantifier (Z3.Expr.ast_of_expr rule) then
          let q = Z3.Quantifier.quantifier_of_expr rule in
          BatArray.of_list (Z3.Quantifier.get_bound_variable_names q), 
          Z3.Quantifier.get_body q
        else BatArray.init 0 (fun _ -> failwith "empty array"), rule
      in
      let decl =  decl_kind matrix in
      let args = Z3.Expr.get_args matrix in
      begin match decl, args with
        | (OP_IMPLIES, [hypo;conc]) ->
          let ind_to_sym = BatHashtbl.create 91 in
          let hypo_decl = decl_kind hypo in
          let (atoms, phi) = 
            begin match hypo_decl with
              | OP_AND ->
                let (rels, phis) = 
                  List.partition 
                    (fun arg -> decl_kind arg = OP_UNINTERPRETED)
                    (Z3.Expr.get_args hypo) 
                in
                let rel_atoms = 
                  List.map 
                    (rel_atom_of_z3 srk rel_ctx ind_to_sym rsym_to_int names)
                    rels
                in
                let phis = List.map (SrkZ3.formula_of_z3 srk) phis in
                rel_atoms, (mk_and srk phis)
              | OP_UNINTERPRETED -> 
                [rel_atom_of_z3 srk rel_ctx ind_to_sym rsym_to_int names hypo],
                mk_true srk
              | OP_OR -> failwith "TODO: OR Case"
              | _ -> [], SrkZ3.formula_of_z3 srk hypo
            end
          in
          let conc, eq_syms = 
            rel_atom_of_z3_fresh srk rel_ctx ind_to_sym rsym_to_int names conc 
          in
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
          let ind_to_sym = BatHashtbl.create 91 in
          let conc = 
            rel_atom_of_z3 srk rel_ctx ind_to_sym rsym_to_int names matrix 
          in
          hypo, conc
        | _ -> failwith "Rule not well formed"
      end
    in
    let parse_query query =
      Hashtbl.find 
        rsym_to_int
        (Z3.Symbol.to_string 
           (Z3.FuncDecl.get_name (Z3.Expr.get_func_decl query)))
    in
    let rules_list = List.map parse_rule (Z3.Fixedpoint.get_rules z3fp) in
    let queries_list = List.map parse_query z3queries in
    let rule_counter = ref (List.length rules_list) in
    let query_counter = ref (List.length queries_list) in
    let rules = Hashtbl.create !rule_counter in
    let queries = Hashtbl.create !query_counter in
    List.iteri (fun ind rule -> Hashtbl.add rules ind rule) rules_list;
    List.iteri (fun ind query -> Hashtbl.add queries ind query) queries_list;
    {rules; rule_counter; queries; query_counter}

  let parse_file ?(context=Z3.mk_context []) srk rel_ctx filename =
    let z3 = context in
    let fp = Z3.Fixedpoint.mk_fixedpoint z3 in
    let z3queries = Z3.Fixedpoint.parse_file fp filename in
    parse_z3fp ~z3queries srk rel_ctx fp

  let parse_string ?(context=Z3.mk_context []) srk rel_ctx filename =
    let z3 = context in
    let fp = Z3.Fixedpoint.mk_fixedpoint z3 in
    let z3queries = Z3.Fixedpoint.parse_string fp filename in
    parse_z3fp ~z3queries srk rel_ctx fp


end
