(* Constrained horn clauses *)
open Syntax
open BatPervasives
module DynArray = BatDynArray
module D = Graph.Pack.Digraph
module WG = WeightedGraph

type relation = int
type rel_atom = relation * symbol list
type 'a fp = { mutable rules : (rel_atom list * 'a formula * rel_atom) list; 
               mutable queries : relation list;
               rel_ctx : (string * typ_fo list) DynArray.t } 


let mk_relation fp ?(name="R") typ =
  DynArray.add fp.rel_ctx (name, typ);
  DynArray.length fp.rel_ctx - 1
let type_of fp rel = snd (DynArray.get fp.rel_ctx rel)
let name_of fp rel = fst (DynArray.get fp.rel_ctx rel)

let rel_of_atom (relation, _) = relation
let params_of_atom (_, params) = params

let typ_symbol_fo srk sym =
  match typ_symbol srk sym with
  | `TyInt -> `TyInt
  | `TyReal -> `TyReal
  | `TyBool -> `TyBool
  (* TODO: arrays *)
  | _ -> assert false

let mk_rel_atom srk fp rel syms =
  if ((type_of fp rel) = (List.map (typ_symbol_fo srk) syms))
  then rel, syms
  else invalid_arg "Type Error mk_rel_atom"

module Relation = struct
  type t = relation 
  module Set = SrkUtil.Int.Set 
  let compare = Stdlib.compare

  let pp fp formatter rel =
    Format.fprintf formatter "@%s:R%n@" (name_of fp rel) rel
  let show fp = SrkUtil.mk_show (pp fp)
end

let pp_rel_atom srk fp formatter (rel, symbols) =
    Format.fprintf formatter "%a(@[%a@])"
      (Relation.pp fp) rel
      (SrkUtil.pp_print_enum_nobox (pp_symbol srk)) (BatList.enum symbols)

let show_rel_atom srk fp = 
  SrkUtil.mk_show (pp_rel_atom srk fp)

module Fp = struct
  type 'a t = 'a fp

  let pp_hypothesis srk fp formatter (rel_atoms, phi) =
    Format.fprintf formatter "(@[";
    SrkUtil.pp_print_enum
      ~pp_sep:(fun formatter () -> Format.fprintf formatter "@ /\\ ")
      (pp_rel_atom srk fp)
      formatter
      (BatList.enum rel_atoms);
    Format.fprintf formatter "@]/\\%a)" (Formula.pp srk) phi
  let pp_rule srk fp formatter (rel_atoms, phi, conc) =
    Format.fprintf formatter "(@[%a@ => %a@])"
      (pp_hypothesis srk fp) (rel_atoms, phi)
      (pp_rel_atom srk fp) conc

  let pp srk formatter fp = 
    Format.fprintf formatter "(Rules:\n@[";
    SrkUtil.pp_print_enum
      ~pp_sep:(fun formatter () -> Format.fprintf formatter "@ \n ")
      (pp_rule srk fp)
      formatter
      (BatList.enum fp.rules);
    Format.fprintf formatter "@]\nQueries:@[%a@])"
      (SrkUtil.pp_print_enum_nobox (Relation.pp fp)) 
      (BatList.enum fp.queries)

  let show srk = SrkUtil.mk_show (pp srk)

  let create () = {rules=[];queries=[];rel_ctx=(DynArray.create ())}

  let add_rule fp hypo phi conc = fp.rules <- (hypo, phi, conc) :: fp.rules 

  let add_query fp query = fp.queries <- query :: fp.queries 

  let get_active_relations fp =
    List.fold_left
      (fun rset (hypo_atoms, _, conc_atom) ->
         List.fold_left
           (fun rset rel_atom -> Relation.Set.add (rel_of_atom rel_atom) rset)
           (Relation.Set.add (rel_of_atom conc_atom) rset)
           hypo_atoms)
      (List.fold_left 
         (fun rset query -> Relation.Set.add query rset)
         Relation.Set.empty
         fp.queries)
      fp.rules

  let get_relations_declared fp =
    BatList.of_enum (0 -- ((DynArray.length fp.rel_ctx) - 1))

  let is_linear rules =
    BatList.fold_left 
      (fun acc (hypo_atoms, _, _) -> acc && (List.length hypo_atoms) <= 1)
      true
      rules

  let mk_eq_by_sort srk s1 s2 =
    assert (typ_symbol srk s1 = typ_symbol srk s2);
    match typ_symbol_fo srk s1 with
    | `TyInt | `TyReal -> mk_eq srk (mk_const srk s1) (mk_const srk s2)
    | `TyBool -> mk_iff srk (mk_const srk s1) (mk_const srk s2)

  let normalize srk fp =
    let rules' =
      List.map (fun (hypos, constr, conc) ->
          let update_atom (atom, eqs, syms) =
            let params, eqs, syms =
              List.fold_right
                (fun param (params, eqs, syms) ->
                   if not (Symbol.Set.mem param syms) then
                     param :: params, eqs, (Symbol.Set.add param syms)
                   else
                     let s = dup_symbol srk param in
                     let eq = mk_eq_by_sort srk s param in
                     s :: params, eq :: eqs, Symbol.Set.add s syms)
                (params_of_atom atom) 
                ([], eqs, syms)
            in
            let atom' = mk_rel_atom srk fp (rel_of_atom atom) params in
            atom', eqs, syms
          in
          let (hypos', eqs, syms) =
            List.fold_left 
              (fun (hypos', eqs, syms) hypo ->
                 let atom', eqs', syms' = update_atom (hypo, eqs, syms) in
                 atom' :: hypos', eqs', syms')
              ([], [],  Symbol.Set.empty)
              hypos
          in
          let (conc', eqs, syms) = update_atom (conc, eqs, syms) in
          let constr' = 
            mk_exists_consts 
              srk 
              (fun s -> Symbol.Set.mem s syms) 
              (mk_and srk (constr :: eqs))
          in
          hypos', constr', conc')
        fp.rules
    in
    {rules=rules'; queries=fp.queries; rel_ctx=fp.rel_ctx} 


  let goal_vert = -2 
  let start_vert = -1
  let emptyarr = BatArray.init 0 (fun _ -> failwith "empty")

  let linchc_to_weighted_graph srk fp pd =
    let fp = normalize srk fp in
    let open WeightedGraph in
    (* The edges of the graph are of the form [(syms', syms', constr)] where 
     * [syms] are the var symbols used in the hypothesis relation, [syms'] are
     * those used in the conclusion relation, and [constr] in the constraint
     * whose free variables are limited to [syms union syms']. Further, [syms]
     * and [syms'] are always disjoint. *)
    let alg = 
      let is_one (_, _, phi) = Formula.equal phi (mk_true srk) in
      let is_zero (_, _, phi) = Formula.equal phi (mk_false srk) in
      let zero = emptyarr, emptyarr, mk_false srk in
      let one = emptyarr, emptyarr, mk_true srk in
      let add x y =
        if is_zero x then y else if is_zero y then x
        else if is_one x || is_one y then one
        else (
          let (prex, postx, phix) = x in
          let (prey, posty, phiy) = y in
          let rhs_new = 
            substitute_sym 
              srk
              (fun sym ->
                 try mk_const srk (prex.(BatArray.findi ((=) sym) prey))
                 with Not_found -> 
                   mk_const srk (postx.(BatArray.findi ((=) sym) posty)))
              phiy
          in
          prex, postx, mk_or srk [phix; rhs_new])
      in
      let mul x y =
        let (prex, postx, phix) = x in
        let (prey, posty, phiy) = y in
        if is_zero x || is_zero y then zero
        else if is_one x then y else if is_one y then x
        else (
          let pre' = Array.map (dup_symbol srk) prex in
          let post' = Array.map (dup_symbol srk) posty in
          let lhs_subst =
            (fun sym ->
               try mk_const srk (pre'.(BatArray.findi ((=) sym) prex))
               with Not_found -> mk_const srk sym)
          in
          let rhs_subst = (fun sym ->
              try mk_const srk (postx.(BatArray.findi ((=) sym) prey))
              with Not_found -> 
                mk_const srk (post'.(BatArray.findi ((=) sym) posty)))
          in
          let phiy' = substitute_sym srk rhs_subst phiy in
          let phix' = substitute_sym srk lhs_subst phix in
          let phi' = 
            mk_exists_consts 
              srk 
              (fun s -> not (Array.mem s postx)) 
              (mk_and srk [phix'; phiy']) 
          in
          (* TODO: try to remove the new quants via miniscoping/del procedure *)
          pre', post', phi')
      in
      let star (pre, post, phi) =
        let module PD = (val pd : Iteration.PreDomain) in
        let (trs, vars) =
          BatArray.fold_lefti
            (fun (trs, vars) ind presym -> 
               (presym, post.(ind)) :: trs, presym :: post.(ind) :: vars)
            ([], [])
            pre
        in
        let lc = mk_symbol srk `TyInt in
        let tf = TransitionFormula.make phi trs in
        let phi' = PD.exp srk trs (mk_const srk lc) (PD.abstract srk tf) in
        let phi' = mk_exists_consts srk (fun s -> List.mem s vars) phi' in
        (* TODO: try to remove the new quants via miniscoping/del procedure *)
        pre, post, phi' 
      in
      {mul; add; star; zero; one}
    in
    let wg = WeightedGraph.add_vertex (WeightedGraph.empty alg) start_vert in
    let wg = WeightedGraph.add_vertex wg goal_vert in
    let wg = 
      List.fold_left 
        (fun wg rel_sym -> WeightedGraph.add_vertex wg rel_sym)
        wg
        (get_relations_declared fp)
    in
    let wg = 
      List.fold_left
        (fun wg (rel_atoms, phi, conc) ->
           match rel_atoms with
           | [] -> 
             WeightedGraph.add_edge 
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
           | _ -> failwith "CHC is non-linear")
        wg
        fp.rules
    in
    let wg =
      List.fold_left
        (fun wg rel -> WeightedGraph.add_edge wg rel alg.one goal_vert)
        wg
        fp.queries
    in
    wg

  let is_super_linear fp =
    (* Initialize graph: One vertex for each rel symbol.
     * There is an edge from rel a to rel b if a occurs in the
     * hypothesis of some rule for which b occurs in the conclusion.
     * A topological sort on the sccs of this graph will determine the
     * ordering on which we need to solve the relations.*)
    let num_rels = (DynArray.length fp.rel_ctx) - 1 in
    let verts = BatArray.init (num_rels + 1) D.V.create in
    let graph = D.create () in
    BatArray.iter (fun v -> D.add_vertex graph v) verts;
    BatList.iter (fun (hypo_atoms, _, conc_atom) ->
        List.iter (fun hatom ->
            D.add_edge 
              graph 
              (verts.(rel_of_atom hatom)) 
              (verts.(rel_of_atom conc_atom)))
          hypo_atoms)
      fp.rules;
    (* We create a new graph in which each scc is collapsed to
     * a single node and there is an edge from scc a to scc b
     * iff scc b was reachable from scc a in the original graph*)
    let sccs = D.Components.scc_array graph in
    let scc_rep = Array.map (fun scc ->  List.hd scc) sccs in
    let path_check = D.PathCheck.create graph in
    let sccverts = BatArray.init (Array.length sccs) D.V.create in
    let sccgraph = D.create () in
    BatArray.iter (fun v -> D.add_vertex sccgraph v) sccverts;
    BatArray.iteri (fun scc1 rel1 ->
        BatArray.iteri (fun scc2 rel2 ->
            if D.PathCheck.check_path path_check rel1 rel2 then
              D.add_edge sccgraph (sccverts.(scc1)) (sccverts.(scc2))
            else ())
          scc_rep)
      scc_rep;
    let solved = Hashtbl.create (num_rels + 1) in
    (* We compute a topologoical sort on the collapsed graph determine
     * if the collapsed graph forms a stratified lin system of chcs.*)
    let (ordering, is_strat) = 
      D.Topological.fold (fun scc_num (ordering, is_stratifiable) ->
          (* First we extract the sub-chc *)
          let of_vert arr v = BatArray.findi ((=) v) arr in
          let rels = 
            Relation.Set.of_list 
              (List.map (of_vert verts) sccs.(of_vert sccverts scc_num)) 
          in
          let ordering' = rels :: ordering in
          let ruleset = 
            List.filter (fun (_, _, conc_atom) ->
                Relation.Set.mem (rel_of_atom conc_atom) rels)
              fp.rules
          in
          let is_stratifiable' = List.fold_left (fun acc (hypo_atoms, _, _) ->
              if List.length (List.filter (fun atom ->
                  not (Hashtbl.mem solved (rel_of_atom atom)))
                  hypo_atoms) > 1
              then false
              else true && acc)
              is_stratifiable
              ruleset
          in
          Relation.Set.iter 
            (fun rel -> Hashtbl.add solved rel ()) 
            rels;
          (ordering', is_stratifiable')
        )
        sccgraph
        ([], true)
    in
    if is_strat then Some (List.rev ordering) else None


  let solve_super_lin srk fp pd ordering =
    let fp = normalize srk fp in
    let num_rels = (DynArray.length fp.rel_ctx) - 1 in
    let solution = Hashtbl.create (num_rels + 1) in
    (* We compute a topologoical sort on the collapsed graph and solve
     * for the relations in order.*)
    List.iter (fun rels ->
        let ruleset = 
          List.filter (fun (_, _, conc_atom) ->
              Relation.Set.mem (rel_of_atom conc_atom) rels)
            fp.rules
        in
        (* Substitute in the solutions for rels calculated at previous strata *)
        let ruleset' = List.map (fun (hypo_atoms, constr, conc) ->
            let hypo_atoms', constr' = 
              List.fold_left (fun (hypo_atoms, constr) atom -> 
                  if Hashtbl.mem solution (rel_of_atom atom) then (
                    let syms, soln = Hashtbl.find solution (rel_of_atom atom) in
                    let subst =
                      (fun sym ->
                         mk_const
                           srk
                           (List.nth
                              (params_of_atom atom)
                              (BatArray.findi ((=) sym) syms)))
                    in
                    let soln = substitute_const srk subst soln in
                    hypo_atoms, mk_and srk [soln; constr])
                  else (atom :: hypo_atoms, constr))
                ([], constr)
                hypo_atoms
            in
            hypo_atoms', constr', conc)
            ruleset
        in
        if is_linear ruleset' then (
          let sub_fp = {rules=ruleset'; queries=[]; rel_ctx=fp.rel_ctx} in
          let wg = linchc_to_weighted_graph srk sub_fp pd in
          let sub_soln = 
            (fun rel -> 
               let _, params, phi = WG.path_weight wg start_vert rel in 
               params, phi) 
          in
          Relation.Set.iter 
            (fun rel -> Hashtbl.add solution rel (sub_soln rel)) 
            rels)
        else (invalid_arg "Chc not super-linear"))
      ordering;
    let goal = 
      mk_or 
        srk 
        (List.map (fun rel -> snd (Hashtbl.find solution rel)) fp.queries) 
    in
    Hashtbl.add solution goal_vert (emptyarr, goal);  
    Hashtbl.find solution


  let query_vc_condition srk fp pd =
    match is_super_linear fp with
    | None -> failwith "No methods for solving non super linear chc systems"
    | Some ordering ->
      let res = solve_super_lin srk fp pd ordering in
      let _, phi = res goal_vert in   
      phi

  let check srk fp pd =
    let phi = query_vc_condition srk fp pd in
    match Quantifier.simsat srk phi with
      | `Unsat  -> `No
      | `Unknown -> `Unknown
      | `Sat -> `Unknown

  let solve srk fp pd =
    match is_super_linear fp with
    | None -> failwith "No methods for solving non lin fp"
    | Some ordering -> solve_super_lin srk fp pd ordering

  let unbooleanize srk fp =
    let fp' = create () in
    let rel_map = BatHashtbl.create (List.length (get_relations_declared fp)) in
    List.iter (fun rel ->
        let typ' = 
          List.map (fun typ -> 
              if typ = `TyBool then `TyInt else typ) 
            (type_of fp rel)
        in
        let rel' = mk_relation fp' ~name:(name_of fp rel) typ' in
        BatHashtbl.add rel_map rel rel')
      (get_relations_declared fp);
    List.iter (fun (hypos, phi, conc) ->
        let sym_map = BatHashtbl.create 97 in
        let map_atom atom =
          let params' = 
            List.map (fun param ->
                if typ_symbol srk param = `TyBool then (
                  if BatHashtbl.mem sym_map param then
                    BatHashtbl.find sym_map param
                  else
                    let param' = mk_symbol srk ~name:(show_symbol srk param) `TyInt in
                    BatHashtbl.add sym_map param param';
                    param')
                else
                  param)
              (params_of_atom atom)
          in
          let rel' = BatHashtbl.find rel_map (rel_of_atom atom) in
          mk_rel_atom srk fp' rel' params'
        in
        let hypos' = List.map map_atom hypos in
        let conc' = map_atom conc in
        let phi_subst = 
          substitute_const 
            srk
            (fun s -> 
               if BatHashtbl.mem sym_map s then
                 mk_eq srk (mk_one srk) (mk_const srk (BatHashtbl.find sym_map s))
               else
                 mk_const srk s)
            phi
        in
        let bool_constrs =
          BatHashtbl.fold (fun _ sym acc -> 
              mk_or 
                srk 
                [mk_eq srk (mk_const srk sym) (mk_one srk);
                 mk_eq srk (mk_const srk sym) (mk_zero srk)] :: acc)
            sym_map
            []
        in
        let phi' = mk_and srk (phi_subst :: bool_constrs) in
        add_rule fp' hypos' phi' conc')
      fp.rules;
    List.iter (fun rel -> 
        add_query fp' (BatHashtbl.find rel_map rel)) 
      fp.queries;
    let rel_fun rel = BatHashtbl.find rel_map rel in
    rel_fun, fp'
end

module ChcSrkZ3 = struct
  
  let typ_of_sort sort =
    let open Z3enums in
    match Z3.Sort.get_sort_kind sort with
    | REAL_SORT -> `TyReal
    | INT_SORT -> `TyInt
    | BOOL_SORT -> `TyBool
    (*| ARRAY_SORT -> `TyArr*)
    |_ -> failwith "function types not currently supported in rel param"

  let rel_atom_of_z3 srk fp ind_to_sym rsym_to_int z3pred =
    let eqs = ref [] in
    let args = List.map 
        (fun arg ->
           begin match Z3.AST.get_ast_kind (Z3.Expr.ast_of_expr arg) with
             | VAR_AST ->
               let index = Z3.Quantifier.get_index arg in
               BatHashtbl.find ind_to_sym index
               (* Logic for handling case if rel atom arg is a numerical
                * or logical constant *)
             | NUMERAL_AST ->
               let sym = mk_symbol srk `TyInt in
               let q = SrkZ3.term_of_z3 srk arg in
               eqs := (mk_eq srk (mk_const srk sym) q) :: !eqs;
               sym
             | APP_AST -> 
               let decl = Z3.Expr.get_func_decl arg in
               begin match Z3.FuncDecl.get_decl_kind decl with
               | OP_TRUE ->
                 let sym = mk_symbol srk `TyBool in
                 eqs := (mk_const srk sym) :: !eqs;
                 sym
               | OP_FALSE -> 
                 let sym = mk_symbol srk `TyBool in
                 eqs := (mk_not srk (mk_const srk sym)) :: !eqs;
                 sym
               | _ -> invalid_arg "Cannot have non-trivial terms as param to relation"
               end
             | _ -> assert false
           end) 
        (Z3.Expr.get_args z3pred) in
    let decl = Z3.Expr.get_func_decl z3pred in
    let rsym = Z3.Symbol.to_string (Z3.FuncDecl.get_name decl) in
    let relation = 
      if Hashtbl.mem rsym_to_int rsym then Hashtbl.find rsym_to_int rsym
      else (
        let typ = List.map (fun arg -> typ_symbol_fo srk arg) args in
        let res = mk_relation fp ~name:rsym typ in
        Hashtbl.add rsym_to_int rsym res;
        res)
    in
    (relation, args), !eqs

  let parse_z3fp ?(z3queries=[]) srk fp z3fp =
    let rsym_to_int = BatHashtbl.create 91 in
    let decl_kind e = Z3.FuncDecl.get_decl_kind (Z3.Expr.get_func_decl e) in
    let parse_rule rule =
      let quanted, matrix =
        if Z3.AST.is_quantifier (Z3.Expr.ast_of_expr rule) then
          let q = Z3.Quantifier.quantifier_of_expr rule in
          List.combine 
            (List.rev (Z3.Quantifier.get_bound_variable_sorts q))
            (List.rev (Z3.Quantifier.get_bound_variable_names q)),
          Z3.Quantifier.get_body q
        else [], rule
      in
      let ind_to_sym = BatHashtbl.create 91 in
      BatList.iteri (fun ind (sort, name) ->
          let sym = 
            mk_symbol srk ~name:(Z3.Symbol.to_string name) (typ_of_sort sort)
          in
          BatHashtbl.add ind_to_sym ind sym) 
        quanted;
      let decl =  decl_kind matrix in
      let args = Z3.Expr.get_args matrix in
      begin match decl, args with
        | (OP_IMPLIES, [hypo;conc]) ->
          let hypo_decl = decl_kind hypo in
          let (atoms, eqs_args, z3phis) = 
            begin match hypo_decl with
              | OP_AND ->
                let (rels, z3phis) = 
                  List.partition 
                    (fun arg -> 
                       Z3.AST.get_ast_kind (Z3.Expr.ast_of_expr arg) = APP_AST
                       && decl_kind arg = OP_UNINTERPRETED)
                    (Z3.Expr.get_args hypo) 
                in
                let rel_atoms, eqs = 
                  List.split 
                    (List.map 
                       (rel_atom_of_z3 srk fp ind_to_sym rsym_to_int)
                       rels)
                in
               rel_atoms, List.flatten eqs, z3phis
              | OP_UNINTERPRETED -> 
                let atom, eqs = 
                  rel_atom_of_z3 srk fp ind_to_sym rsym_to_int hypo 
                in
                [atom], eqs, []
              | _ -> [], [], [hypo] 
            end
          in
          let conc, eqs_args_conc = 
            rel_atom_of_z3 srk fp ind_to_sym rsym_to_int conc 
          in
          let phi = mk_and srk (List.map (SrkZ3.formula_of_z3 srk) z3phis) in
          let phi = 
            substitute 
              srk 
              (fun (i, _) -> mk_const srk (BatHashtbl.find ind_to_sym i)) 
              phi 
          in 
          let phi = mk_and srk (phi :: eqs_args @ eqs_args_conc) in
          atoms, phi, conc
        | (OP_UNINTERPRETED, _) ->
          let conc, eqs = 
            rel_atom_of_z3 srk fp ind_to_sym rsym_to_int matrix 
          in
          [], mk_and srk eqs, conc
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
    {rules; queries;rel_ctx=fp.rel_ctx}

  let parse_file ?(ctx=Z3.mk_context []) srk fp filename =
    let z3 = ctx in
    let z3fp = Z3.Fixedpoint.mk_fixedpoint z3 in
    let z3queries = Z3.Fixedpoint.parse_file z3fp filename in
    parse_z3fp ~z3queries srk fp z3fp

  let parse_string ?(ctx=Z3.mk_context []) srk fp str =
    let z3 = ctx in
    let z3fp = Z3.Fixedpoint.mk_fixedpoint z3 in
    let z3queries = Z3.Fixedpoint.parse_string z3fp str in
    parse_z3fp ~z3queries srk fp z3fp
end
