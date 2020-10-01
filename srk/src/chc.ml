(* Constrainted horn clauses *)
open Syntax
module DynArray = BatDynArray

type relation = int
type relcontext = (string * typ list) DynArray.t
type relation_atom = relation * symbol list
type 'a hypothesis = relation_atom list * 'a formula
type 'a rule = 'a hypothesis * relation_atom
type query = relation
type 'a chc = {rules : 'a rule list; queries : query list}

let mk_relcontext = DynArray.create ()

let mk_relation rel_ctx ?(name="R") typ =
  DynArray.add rel_ctx (name, typ);
  DynArray.length rel_ctx - 1
let type_of rel_ctx rel = snd (DynArray.get rel_ctx rel)
let name_of rel_ctx rel = fst (DynArray.get rel_ctx rel)

let rel_of_atom (relation, _) = relation
let params_of_atom (_, params) = params

let mk_rel_atom srk rel_ctx rel syms =
  BatList.iter2
    (fun arg_typ sym_typ -> 
       if arg_typ = sym_typ then ()
       else failwith "Types Error Rel Atom")
    (type_of rel_ctx rel)
    (List.map (typ_symbol srk) syms);
  rel, syms

let mk_hypo atoms phi = atoms, phi
let mk_rule hypo atom = hypo, atom

module Relation = struct
  type t = relation 
  module Set = SrkUtil.Int.Set 
  let compare = Stdlib.compare

  let pp rel_ctx formatter rel =
    Format.fprintf formatter "@%s:R%n@" (name_of rel_ctx rel) rel
  let show rel_ctx = SrkUtil.mk_show (pp rel_ctx)
end



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
let pp_query = Relation.pp

let show_relation_atom srk rel_ctx = 
  SrkUtil.mk_show (pp_relation_atom srk rel_ctx)
let show_hypothesis srk rel_ctx = SrkUtil.mk_show (pp_hypothesis srk rel_ctx)
let show_rule srk rel_ctx = SrkUtil.mk_show (pp_rule srk rel_ctx)
let show_query rel_ctx = SrkUtil.mk_show (pp_query rel_ctx)

module Chc = struct
  type 'a t = 'a chc 

  let pp srk rel_ctx formatter chc = 
    Format.fprintf formatter "(Rules:\n@[";
    SrkUtil.pp_print_enum
      ~pp_sep:(fun formatter () -> Format.fprintf formatter "@ \n ")
      (pp_rule srk rel_ctx)
      formatter
      (BatList.enum chc.rules);
    Format.fprintf formatter "@]\nQueries:@[%a@])"
    (SrkUtil.pp_print_enum_nobox (pp_query rel_ctx)) 
      (BatList.enum chc.queries)


  let show srk rel_ctx = SrkUtil.mk_show (pp srk rel_ctx)

  let create = {rules=[];queries=[]}
  let chc_of rules queries = {rules; queries}

  let add_rule chc rule = {rules=rule::chc.rules; queries=chc.queries} 
  let add_query chc query = {rules=chc.rules; queries=query::chc.queries}
  let get_rules chc = chc.rules
  let get_queries chc = chc.queries

  let get_relations_used chc =
    List.fold_left
      (fun rset ((hypo_atoms, _), conc_atom) ->
         List.fold_left
           (fun rset rel_atom -> Relation.Set.add (rel_of_atom rel_atom) rset)
           (Relation.Set.add (rel_of_atom conc_atom) rset)
           hypo_atoms)
      (List.fold_left 
         (fun rset query -> Relation.Set.add query rset)
         Relation.Set.empty
         chc.queries)
      chc.rules

  let is_linear chc =
    BatList.fold_left 
      (fun acc ((rel_atoms, _), _) -> acc && (List.length rel_atoms) <= 1)
      true
      chc.rules

  let goal_vert = -2 
  let start_vert = -1 
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
          let rhs_pre_postmap = 
            map_union (mk_subst_map post2 post') (mk_subst_map pre2 post1)
          in
          let rhs_subst =
            Memo.memo 
              ~size:(Symbol.Set.cardinal (symbols phi2))
              (fun sym -> 
                 if Symbol.Map.mem sym rhs_pre_postmap then
                   Symbol.Map.find sym rhs_pre_postmap
                 else (
                   mk_const 
                     srk
                     (mk_symbol 
                        srk 
                        ~name:(show_symbol srk sym) 
                        (typ_symbol srk sym))))
          in
          let phi2 = substitute_const srk rhs_subst phi2 in
          let phi1 = substitute_map srk (mk_subst_map pre1 pre') phi1 in
          pre', post', mk_and srk [phi1; phi2]
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
    let wg = WeightedGraph.add_vertex (WeightedGraph.empty alg) start_vert in
    let wg = WeightedGraph.add_vertex wg goal_vert in
    let wg = Relation.Set.fold 
        (fun rel_sym wg -> WeightedGraph.add_vertex wg rel_sym)
        (get_relations_used chc)
        wg
    in
    let wg = 
      List.fold_left
        (fun wg ((rel_atoms, phi), conc) ->
           match rel_atoms with
           | [] -> WeightedGraph.add_edge 
                     wg 
                     start_vert
                     (emptyarr, BatArray.of_list (params_of_atom conc), phi)
                     (rel_of_atom conc)
           | [hd] ->
             WeightedGraph.add_edge 
               wg 
               (rel_of_atom hd)
               (BatArray.of_list (params_of_atom hd), 
                BatArray.of_list (params_of_atom conc), 
                phi)
               (rel_of_atom conc)
           | _ -> failwith "Rule with multiple relations in hypothesis")
        wg
        chc.rules
    in
    let wg =
      List.fold_left
        (fun wg rel -> 
           WeightedGraph.add_edge
             wg
             rel
             alg.one
             goal_vert)
        wg
        chc.queries
    in
    wg

  let has_reachable_goal srk chc pd = 
    if is_linear chc then (
      let wg = to_weighted_graph srk chc pd in
      let _, _, phi = WeightedGraph.path_weight wg start_vert goal_vert in
      begin match Smt.is_sat srk phi with
        | `Unsat -> `No
        | `Unknown -> `Unknown
        | `Sat -> `Unknown
      end)
    else failwith "No methods for solving non lin chc"

  let solve srk chc pd =
    if is_linear chc then (
      let wg = to_weighted_graph srk chc pd in
      let soln = 
        (fun rel -> 
           let _, params, phi = WeightedGraph.path_weight wg start_vert rel in 
           params, phi) 
      in
      soln)
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
        let res = mk_relation rel_ctx ~name:rsym typ in
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
               :: [mk_eq_syms srk eq_syms])
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
    let rules = List.map parse_rule (Z3.Fixedpoint.get_rules z3fp) in
    let queries = List.map parse_query z3queries in
    {rules; queries}

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
