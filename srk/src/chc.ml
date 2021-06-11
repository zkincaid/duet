(* Constrained horn clauses *)
open Syntax
(*open BatPervasives*)
module DynArray = BatDynArray
module D = Graph.Pack.Digraph
module WG = WeightedGraph

type proposition = { symbol : symbol; names : string list }
module Proposition = struct
  (* Relation atoms have as parameters free variables. We maintain the invariant
   * that these free variables be sequential. The int option in this type
   * describes the debruijn index of the first parameter; it is `None` in the
   * case that the atom has no parameters.*)
  type t = proposition
 
  let symbol_of prop  = prop.symbol
  let names_of prop = prop.names


  let typ_of_params srk prop =
    match typ_symbol srk prop.symbol with 
    | `TyBool 
    | `TyFun ([], `TyBool) -> []
    | `TyFun (lst, `TyBool) -> lst
    | _ -> assert false

  let prop_of srk prop init_index =
    let params = 
      BatList.mapi (fun ind typ ->
          mk_var srk (ind + init_index) typ)
        (typ_of_params srk prop)
    in
    mk_app srk (symbol_of prop) params

  let mk_proposition srk symbol names =
    match typ_symbol srk symbol with 
    | `TyBool when BatList.is_empty names -> { symbol; names}
    | `TyFun (typs, `TyBool) when List.length names = List.length typs ->
      { symbol; names}
    | _ -> invalid_arg "mk_proposition: ill-formed proposition"
end

 type 'a fp = { rules : (proposition * proposition list * 'a formula) list; 
                queries : Symbol.Set.t }

let typ_symbol_fo srk sym =
  match typ_symbol srk sym with
  | `TyInt -> `TyInt
  | `TyReal -> `TyReal
  | `TyBool -> `TyBool
  | `TyArr -> `TyArr
  (* TODO: arrays *)
  | _ -> assert false

module Fp = struct
  type 'a t = 'a fp

  let pp_rule srk formatter (conc, hypo_props, phi) =
    let body, _ =
      List.fold_left (fun (phi, counter) prop -> 
          mk_and srk [Proposition.prop_of srk prop counter; phi], 
          counter + List.length (Proposition.typ_of_params srk prop)) 
        (phi, List.length (Proposition.typ_of_params srk conc))
        hypo_props
    in
    let pre_quantified = mk_if srk body (Proposition.prop_of srk conc 0) in
    let phi = 
      List.fold_left (fun phi prop ->
          BatList.fold_left2 (fun phi typ name ->
              mk_forall srk ~name:name typ phi)
            phi
            (Proposition.typ_of_params srk prop)
            (Proposition.names_of prop))
        pre_quantified
        (conc :: hypo_props)
    in
    Formula.pp srk formatter phi

  let pp srk formatter fp = 
    Format.fprintf formatter "(Rules:\n@[";
    SrkUtil.pp_print_enum
      ~pp_sep:(fun formatter () -> Format.fprintf formatter "@ \n ")
      (pp_rule srk)
      formatter
      (BatList.enum fp.rules);
    Format.fprintf formatter "@]\nQueries:@[%a@])"
      (SrkUtil.pp_print_enum_nobox (pp_symbol srk)) 
      (Symbol.Set.enum fp.queries)

  let show srk = SrkUtil.mk_show (pp srk)

  let empty = {rules=[];queries=Symbol.Set.empty}

  let add_rule fp conc hypo phi = { fp with rules = (conc, hypo, phi) :: fp.rules} 

  let add_query fp query = { fp with queries = Symbol.Set.add query fp.queries} 

  let goal_vert = -2 
  let start_vert = -1

  let linchc_to_weighted_graph srk (fp : 'a t) pd =
    let open WeightedGraph in
    (* The edges of the graph are of the form 
     * [(conc params, hypo params, constr)]*) 
    let alg = 
      let is_one (_, _, phi) = Formula.equal phi (mk_true srk) in
      let is_zero (_, _, phi) = Formula.equal phi (mk_false srk) in
      let zero = [], [], mk_false srk in
      let one = [], [], mk_true srk in
      let add x y =
        if is_zero x then y else if is_zero y then x
        else (
          let (fvc, fvh, phix) = x in
          let (_, _, phiy) = y in
          fvc, fvh, mk_or srk [phix; phiy])
      in
      let mul x y =
        let (_, p_hx, phix) = x in
        let (p_cy, p_hy, phiy) = y in
        if is_one x then y else if is_one y then x
        else (
          let num_p_cy, num_p_hy = List.length p_cy, List.length p_hy in
          let phiy' = 
            substitute
              srk
              (fun (ind, typ) ->
                 if ind < num_p_cy
                 then mk_var srk (ind + num_p_hy) typ
                 else mk_var srk (ind - num_p_cy) typ)
              phiy
          in
          let phix' =
            substitute
              srk
              (fun (ind, typ) ->
                 if ind < num_p_hy 
                 then mk_var srk ind typ
                 else mk_var srk (ind + num_p_cy) typ)
              phix
          in
          let phi' =
            List.fold_left (fun phi (name, typ) ->
                mk_exists srk ~name typ phi)
              (mk_and srk [phix'; phiy'])
              p_hy
          in
          (* TODO: try to remove the new quants via miniscoping/del procedure *)
          p_cy, p_hx, phi')
      in
      let star (p_c, p_h, phi) =
        (* TODO: can use better data types more efficiently here *)
        let skolems = symbols phi in
        let exists sym = not (Symbol.Set.mem sym skolems) in 
        let trs = 
          List.map (fun (name, typ) ->
              let s1 = mk_symbol srk ~name (typ :> typ) in
              let s2 = mk_symbol srk ~name:(name^"'") (typ :> typ) in
              s1, s2)
            p_c
        in
        let hypo_vars, conc_vars = List.split trs in
        let vars = conc_vars @ hypo_vars in
        let phi =
          substitute
            srk
            (fun (ind, _) ->
               if ind < List.length p_c
               then mk_const srk (snd (List.nth trs ind))
               else mk_const srk (fst (List.nth trs (ind - List.length p_c))))
            phi
        in
        let module PD = (val pd : Iteration.PreDomain) in
        let lc = mk_symbol srk `TyInt in
        let tf = TransitionFormula.make ~exists phi trs in
        let phi' = PD.exp srk trs (mk_const srk lc) (PD.abstract srk tf) in
        let trs_flat = List.flatten (List.map (fun (x, x') -> [x; x']) trs) in
        let phi' = mk_exists_consts srk (fun s -> Symbol.Set.mem s skolems || List.mem s trs_flat) phi' in
        let phi' =
          substitute_sym 
            srk
            (fun sym ->
              match BatList.index_of sym vars with
              | Some i -> mk_var srk i (typ_symbol_fo srk sym)
              | None -> mk_const srk sym)
            phi'
        in
        (* TODO: try to remove the new quants via miniscoping/del procedure *)
        p_c, p_h, phi' 
      in
      {mul; add; star; zero; one}
    in
    let wg = WeightedGraph.add_vertex (WeightedGraph.empty alg) start_vert in
    let wg = WeightedGraph.add_vertex wg goal_vert in
    let prop_symbols =
      BatList.fold_left (fun props (conc, hypo, _) ->
          BatList.fold_left (fun props prop ->
              Symbol.Set.add prop.symbol props)
            props
            (conc ::hypo))
        fp.queries
        fp.rules
    in
    let wg = 
      Symbol.Set.fold (fun prop_sym wg -> 
          WeightedGraph.add_vertex wg (int_of_symbol prop_sym))
        prop_symbols
        wg
    in
    let wg  = 
      List.fold_left
        (fun wg (conc, hypo_props, constr) ->
           match hypo_props with
           | [] -> 
             WeightedGraph.add_edge 
               wg 
               start_vert
               (BatList.combine conc.names (Proposition.typ_of_params srk conc), [], constr)
               (int_of_symbol conc.symbol)
           | [hd] -> 
             WeightedGraph.add_edge 
               wg
               (int_of_symbol hd.symbol)
               (BatList.combine conc.names (Proposition.typ_of_params srk conc),
                BatList.combine conc.names (Proposition.typ_of_params srk hd),
                constr)
               (int_of_symbol conc.symbol)
           | _ -> failwith "CHC is non-linear")
        wg
        fp.rules
    in
    let wg =
      Symbol.Set.fold (fun sym wg ->
          WeightedGraph.add_edge wg (int_of_symbol sym) alg.one goal_vert)
        fp.queries
        wg
    in
    wg

  let stratify fp =
    (* Initialize graph: One vertex for each rel symbol.
     * There is an edge from rel a to rel b if a occurs in the
     * hypothesis of some rule for which b occurs in the conclusion.
     * A topological sort on the sccs of this graph will determine the
     * ordering on which we need to solve the relations.*)
    let prop_symbols =
      BatList.fold_left (fun props (conc, hypo, _) ->
          BatList.fold_left (fun props prop ->
              Symbol.Set.add prop.symbol props)
            props
            (conc ::hypo))
        fp.queries
        fp.rules
    in
    let num_rels =  Symbol.Set.cardinal prop_symbols in
    let verts = BatHashtbl.create 97 in
    let inv_verts = BatHashtbl.create 97 in
    Symbol.Set.iter (fun sym ->
        let vert = D.V.create (int_of_symbol sym) in
        BatHashtbl.add verts sym vert;
        BatHashtbl.add inv_verts vert sym)
      prop_symbols; 
    let graph = D.create () in
    BatHashtbl.iter (fun _ v -> D.add_vertex graph v) verts;
    BatList.iter (fun (conc, hypo, _) ->
        List.iter (fun h_prop ->
            D.add_edge 
              graph 
              (BatHashtbl.find verts h_prop.symbol) 
              (BatHashtbl.find verts conc.symbol))
          hypo)
      fp.rules;
    (* We create a new graph in which each scc is collapsed to
     * a single node and there is an edge from scc a to scc b
     * iff scc b was reachable from scc a in the original graph*)
    let sccs = D.Components.scc_list graph in
    let solved = Hashtbl.create num_rels in
    (* We compute a topologoical sort on the collapsed graph determine
     * if the collapsed graph forms a stratified lin system of chcs.*)
    let (ordering, is_strat) =
      BatList.fold_left (fun (ordering, is_strat) verts ->
          (* First we extract the sub-chc *)
          let props = Symbol.Set.of_list (List.map (BatHashtbl.find inv_verts) verts) in
          let ordering' = props :: ordering in
          let ruleset = 
            List.filter (fun (conc, _, _) -> 
                Symbol.Set.mem conc.symbol props)
              fp.rules
          in
          let is_strat' = List.fold_left (fun acc (_, hypo_props, _) ->
              if List.length (List.filter (fun prop ->
                  not (Hashtbl.mem solved prop.symbol))
                  hypo_props) > 1
              then (false)
              else true && acc)
              is_strat
              ruleset
          in
          Symbol.Set.iter 
            (fun rel -> Hashtbl.add solved rel ()) 
            props;
          (ordering', is_strat')
        )
        ([], true)
        (List.rev sccs)
    in
    if is_strat then Some (List.rev ordering) else None


  let solve_super_lin srk fp pd ordering =
    let solution = Hashtbl.create 97 in
    (* We compute a topologoical sort on the collapsed graph and solve
     * for the relations in order.*)
    List.iter (fun rels ->
        let ruleset = 
          List.filter (fun (conc, _, _) ->
              Symbol.Set.mem conc.symbol rels)
            fp.rules
        in
        (* Substitute in the solutions for rels calculated at previous strata *)
        let ruleset' = List.map (fun (conc, hypo_props, constr) ->
            let hypo_atoms', constr', _ = 
              List.fold_left (fun (hypo_atoms, constr, param_counter) prop -> 
                  let num_params = List.length (Proposition.typ_of_params srk prop) in
                  if Hashtbl.mem solution (int_of_symbol prop.symbol) then (
                    let soln = Hashtbl.find solution (int_of_symbol prop.symbol) in
                    let constr = 
                      substitute
                        srk
                        (fun (ind, typ) ->
                           if ind < param_counter
                           then mk_var srk (ind + num_params) typ
                           else if ind >= param_counter && ind < param_counter + num_params
                           then mk_var srk (ind - param_counter) typ
                           else mk_var srk ind typ)
                        constr
                    in
                    let constr = mk_and srk [soln; constr] in
                    let qs = BatList.combine prop.names (Proposition.typ_of_params srk prop) in
                    let constr =
                      BatList.fold_left (fun constr (name, typ) ->
                          mk_exists srk ~name typ constr)
                        constr
                        qs
                    in
                    hypo_atoms, constr, param_counter)
                  else (prop :: hypo_atoms, constr, param_counter + num_params))
                ([], constr, List.length (Proposition.typ_of_params srk conc))
                hypo_props
            in
            conc, List.rev hypo_atoms', constr')
            ruleset
        in
        let sub_fp = {rules=ruleset'; queries=Symbol.Set.empty} in
        let wg = linchc_to_weighted_graph srk sub_fp pd in
        let sub_soln = 
          (fun rel -> 
             let _, _, phi = WG.path_weight wg start_vert rel in 
             phi) 
        in
        Symbol.Set.iter 
          (fun rel -> Hashtbl.add solution (int_of_symbol rel) (sub_soln (int_of_symbol rel))) 
          rels)
      ordering;
    let goal = 
      mk_or 
        srk 
        (List.map (fun rel -> (Hashtbl.find solution (int_of_symbol rel))) (Symbol.Set.to_list fp.queries))
    in
    Hashtbl.add solution goal_vert goal;  
    Hashtbl.find solution


  let query_vc_condition srk fp pd =
    match stratify fp with
    | None -> failwith "No methods for solving non super linear chc systems"
    | Some ordering ->
      let res = solve_super_lin srk fp pd ordering in
      res goal_vert   

  let check srk fp pd =
    let phi = query_vc_condition srk fp pd in
    match Quantifier.simsat srk phi with
      | `Unsat  -> `No
      | `Unknown -> `Unknown
      | `Sat -> `Unknown

  let solve srk fp pd =
    match stratify fp with
    | None -> failwith "No methods for solving non lin fp"
    | Some ordering -> solve_super_lin srk fp pd ordering

end

module ChcSrkZ3 = struct
  open SrkZ3

  let typ_of_sort sort =
    let open Z3enums in
    match Z3.Sort.get_sort_kind sort with
    | REAL_SORT -> `TyReal
    | INT_SORT -> `TyInt
    | BOOL_SORT -> `TyBool
    | ARRAY_SORT -> `TyArr
    | _ -> invalid_arg "typ_of_sort"


  let parse_z3fp ?(z3queries=[]) srk z3fp =
    let cos =
      Memo.memo (fun (name, typ) ->
          mk_symbol srk ~name typ)
    in
    let sym_of_decl =
      fun decl ->
        let open Z3 in
        let sym = FuncDecl.get_name decl in
        match FuncDecl.get_domain decl with
        | [] ->
          cos (Symbol.to_string sym, typ_of_sort (FuncDecl.get_range decl))
        | dom ->
          let typ =
            `TyFun (List.map typ_of_sort dom,
                    typ_of_sort (FuncDecl.get_range decl))
          in
          cos (Symbol.to_string sym, typ)
    in
    let rec detach_qpf qnf_phi : (string * typ_fo) list * 'a formula =
      match Formula.destruct srk qnf_phi with
      | `Quantify (`Forall, name, typ, phi) -> 
        let qts, phi = detach_qpf phi in
        (name, typ) :: qts, phi
      | `Quantify (`Exists, _, _, _) -> assert false
      | matrix -> [], Formula.construct srk matrix
    in
    let detach_conc matrix = 
      match Formula.destruct srk matrix with
      | `Proposition (`App (f, args)) -> mk_true srk, (f, args)
      | `Or [n_hypo; conc] ->
        begin match Formula.destruct srk n_hypo, Formula.destruct srk conc with
          | `Not hypo, `Proposition (`App (f, args)) -> hypo, (f, args)
          | _ -> assert false
        end
      | _ -> assert false
    in
    let detach_hypo_props hypo =
      match Formula.destruct srk hypo with
      | `Proposition (`App (f, args)) -> [(f, args)], mk_true srk
      | `And conjs ->
        let (props, constr_conjs) = 
          BatList.partition_map (fun conj -> 
               match Formula.destruct srk conj with
               | `Proposition (`App (f, args)) -> Left (f, args)
               | phi -> Right (Formula.construct srk phi))
            conjs 
        in
        props, mk_and srk constr_conjs
      | _ -> [], hypo
    in
    let mk_eq_by_typ typ ind1 ind2 = 
      let var1 = mk_var srk ind1 typ in
      let var2 = mk_var srk ind2 typ in
      match typ with
      | `TyBool -> mk_iff srk var1 var2
      | `TyReal
      | `TyInt -> mk_eq srk var1 var2
      | `TyArr -> mk_arr_eq srk var1 var2
    in 
    (* This handles all of the logic for taking in the srk style propositions
     * and deriving the chc style propositions. We return a tuple containing
     * 1) a map from the original fvs to the news fvs
     * 2) the chc style props (func symbol + names of params)
     * 3) formulae that need to be added to the constraint as a result of the
     * conversion from srk style props to chc style props*)
    let parse_props props qpf =
      let fv_order = Hashtbl.create 97 in
      let cnter = ref (-1) in
      let phis = ref [] in
      List.map (fun (symbol, args) ->
          {symbol;
           names = 
             List.mapi (fun ind_arg arg ->
                 cnter := !cnter + 1;
                 match destruct srk arg with
                 | `Real q -> 
                   let typ, typ_fun =
                     match typ_symbol srk symbol with
                     | `TyFun (lst, _) ->
                       if List.nth lst ind_arg = `TyInt 
                       then `TyInt, fun s -> QQ.to_zz s |> Option.get |> mk_zz srk
                       else `TyReal, mk_real srk
                     | _ -> assert false
                   in
                   phis := mk_eq srk (typ_fun q) (mk_var srk !cnter typ) :: !phis;
                   "k"
                 | `Tru ->
                   phis := (mk_var srk !cnter `TyBool) :: !phis;
                   "b"
                 | `Fls ->
                   phis := mk_not srk (mk_var srk !cnter `TyBool) :: !phis;
                   "b"
                 | `Var (i, typ) ->
                   if Hashtbl.mem fv_order i then (
                     let i2 = Hashtbl.find fv_order i in
                     phis := mk_eq_by_typ (typ :> typ_fo) !cnter i2 :: !phis)
                   else (Hashtbl.add fv_order i !cnter);
                   fst (List.nth qpf i)
                 | `Proposition (`Var i) ->
                   if Hashtbl.mem fv_order i then (
                     let i2 = Hashtbl.find fv_order i in
                     phis := mk_eq_by_typ `TyBool !cnter i2 :: !phis)
                   else (Hashtbl.add fv_order i !cnter);
                   fst (List.nth qpf i)
                 | _ -> assert false)
               args})
        props,
      fv_order,
      !phis
    in
    let non_prop_fvs constr prop_fv_map (qpf : (string * typ_fo) list) =
      let fv_map = Hashtbl.create 97 in
      BatHashtbl.fold (fun ind _ (counter, qinfos) ->
          if Hashtbl.mem prop_fv_map ind then (counter, qinfos)
          else (
            Hashtbl.add fv_map ind counter;
            (counter + 1, List.nth qpf ind :: qinfos)))
        (free_vars constr)
        (0, []),
      fv_map
    in
    let parse_rule rule =
      let rule = formula_of_z3 srk ~sym_of_decl rule in
      let qnf_rule = Formula.prenex srk rule in
      let qpf_rev, matrix = detach_qpf qnf_rule in
      let qpf = List.rev qpf_rev in
      let hypo, conc_prop = detach_conc matrix in
      let hypo_props, constr = detach_hypo_props hypo in
      let props, prop_fvs, phis = parse_props (conc_prop :: hypo_props) qpf in
      (* The constr cannot have any free vars other than those used as an
       * argument to a proposition. For the remaining fvs, we will bound them
       * with quantifiers in the constraint. This requires reordering the fvs
       * so that the non-prop fvs are the smaller debruijn indices. 
       * These next few lines of code handles that. *)
      let (num, qinfos), non_prop_fv_map = non_prop_fvs constr prop_fvs qpf in
      let constr =
        substitute
          srk
          (fun (ind, typ) ->
             if Hashtbl.mem prop_fvs ind then
               mk_var srk (num + (Hashtbl.find prop_fvs ind)) typ
             else mk_var srk (Hashtbl.find non_prop_fv_map ind) typ)
          constr
      in
      let constr = mk_and srk (constr :: phis) in
      let constr =
        BatList.fold_left (fun constr (name, typ) ->
            mk_exists srk ~name typ constr)
          constr
          (List.rev qinfos)
      in
      List.hd props, List.tl props, constr
    in
    let parse_query query = sym_of_decl (Z3.Expr.get_func_decl query) in
    let rules = List.map parse_rule (Z3.Fixedpoint.get_rules z3fp) in
    let queries = Symbol.Set.of_list (List.map parse_query z3queries) in
    {rules; queries}

  let parse_file ?(ctx=Z3.mk_context []) srk filename =
    let z3 = ctx in
    let z3fp = Z3.Fixedpoint.mk_fixedpoint z3 in
    let z3queries = Z3.Fixedpoint.parse_file z3fp filename in
    parse_z3fp ~z3queries srk z3fp

  let parse_string ?(ctx=Z3.mk_context []) srk str =
    let z3 = ctx in
    let z3fp = Z3.Fixedpoint.mk_fixedpoint z3 in
    let z3queries = Z3.Fixedpoint.parse_string z3fp str in
    parse_z3fp ~z3queries srk z3fp
end
