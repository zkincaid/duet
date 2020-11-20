(* Constrained horn clauses *)
open Syntax
open BatPervasives
module DynArray = BatDynArray

type relation = int
type rel_atom = relation * symbol list
type 'a fp = {mutable rules : (rel_atom list * 'a formula * rel_atom) list; 
              mutable queries : relation list;
              rel_ctx : (string * typ list) DynArray.t} 


let time s =
    let t = Unix.gettimeofday () in
    Log.errorf "\n%s Curr time: %fs\n" s (t); t

let diff t1 t2 s =
    Log.errorf "\n%s Execution time: %fs\n" s (t2 -. t1)



let mk_relation fp ?(name="R") typ =
  DynArray.add fp.rel_ctx (name, typ);
  DynArray.length fp.rel_ctx - 1
let type_of fp rel = snd (DynArray.get fp.rel_ctx rel)
let name_of fp rel = fst (DynArray.get fp.rel_ctx rel)

let rel_of_atom (relation, _) = relation
let params_of_atom (_, params) = params

let mk_rel_atom srk fp rel syms =
  if ((type_of fp rel) = (List.map (typ_symbol srk) syms))
  then rel, syms
  else failwith "Types Error Rel Atom"

let is_array_sym srk sym = typ_symbol srk sym = `TyFun([`TyInt], `TyInt)


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

  let get_relations_used fp =
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

  let is_linear fp =
    BatList.fold_left 
      (fun acc (hypo_atoms, _, _) -> acc && (List.length hypo_atoms) <= 1)
      true
      fp.rules

  let goal_vert = -2 
  let start_vert = -1 
  let to_weighted_graph srk fp pd =
    let stars_test = ref 0 in
    let open WeightedGraph in
    let emptyarr = BatArray.init 0 (fun _ -> failwith "empty") in
    let alg = 
      let sym_args sym =
        if is_array_sym srk sym then [mk_var srk 0 `TyInt] else []
      in
      let is_one (_, _, phi) = Formula.equal phi (mk_true srk) in
      let is_zero (_, _, phi) = Formula.equal phi (mk_false srk) in
      let zero = emptyarr, emptyarr, mk_false srk in
      let one = emptyarr, emptyarr, mk_true srk in
      let add x y =
        let t1  = time "IN ADD" in
        let (x, y, res) = if is_zero x then y else if is_zero y then x
          else if is_one x || is_one y then one
          else (
            let (pre, post, _) = x in
            let pre' = Array.map (fun sym -> dup_symbol srk sym) pre in
            let post' = Array.map (fun sym -> dup_symbol srk sym) post in
            let subst (pre, post, phi) =
              substitute_sym 
                srk
                (fun sym ->
                   if Array.mem sym pre then
                     mk_app 
                       srk 
                       (pre'.(BatArray.findi (fun s -> s = sym) pre))
                       (sym_args sym)
                   else if Array.mem sym post then
                     mk_app 
                       srk 
                       (post'.(BatArray.findi (fun s -> s = sym) post))
                       (sym_args sym)
                   else mk_app srk sym (sym_args sym))
                phi
            in
            pre', post', mk_or srk [subst x; subst y])
        in
        let t2 = time "OUT ADD" in
        diff t1 t2 "ADD";
        to_file srk res "/Users/jakesilverman/Documents/duet/duet/add.smt2";
        (x, y, res)

      in
      let mul x y =
        let t1 = time "IN MUL" in
        let (pre1, post1, phi1) = x in
        let (pre2, post2, phi2) = y in
        to_file srk phi1 "/Users/jakesilverman/Documents/duet/duet/mul1.smt2";
        to_file srk phi2 "/Users/jakesilverman/Documents/duet/duet/mul2.smt2";
        let (x, y, res) = 
          if is_zero x || is_zero y then zero
          else if is_one x then y else if is_one y then x
          else (
            Log.errorf "DOING THE MUL THING";
            let pre' = Array.map (fun sym -> dup_symbol srk sym) pre1 in
            let post' = Array.map (fun sym -> dup_symbol srk sym) post2 in
            let lhs_subst =
              (fun sym ->
                 if Array.mem sym pre1 then
                   mk_app 
                     srk 
                     (pre'.(BatArray.findi (fun s -> s = sym) pre1))
                     (sym_args sym)
                 else mk_app srk sym (sym_args sym))
            in
            let rhs_subst =
              Memo.memo 
                ~size:((Symbol.Set.cardinal (symbols phi2) * 4/3))
                (fun sym -> 
                   if Array.mem sym pre2 then
                     mk_app 
                       srk 
                       (post1.(BatArray.findi (fun s -> s = sym) pre2))
                       (sym_args sym)
                   else if Array.mem sym post2 then
                     mk_app 
                       srk 
                       (post'.(BatArray.findi (fun s -> s = sym) post2))
                       (sym_args sym)
                   else mk_app srk (dup_symbol srk sym) (sym_args sym))
            in
            let phi2 = substitute_sym srk rhs_subst phi2 in
            let phi1 = substitute_sym srk lhs_subst phi1 in
            pre', post', mk_and srk [phi1; phi2]
          )
        in
        let t2 = time "OUT MUL" in
        diff t1 t2 "MUL";
        to_file srk res "/Users/jakesilverman/Documents/duet/duet/mul.smt2";
        (x, y, res)
      in
      let star (pre, post, phi) = Log.errorf "\n\nEMPEMPEMP\n\n";
        let t1 = time "STAR IN" in
        stars_test := 1 + !stars_test;
        to_file srk phi "/Users/jakesilverman/Documents/duet/duet/star.smt2";
        let module PD = (val pd : Iteration.PreDomain) in
        let trs =
          BatArray.fold_lefti
            (fun trs ind presym -> (presym, post.(ind)) :: trs)
            []
            pre
        in
        let lc = mk_symbol srk `TyInt in
        let flag_sym = mk_symbol srk ~name:"FLAG" `TyBool in
        let tr_phi = TransitionFormula.make phi trs in
        let res = 
          if !stars_test = 3 then (
            let tr_phi = TransitionFormula.make phi ((flag_sym, flag_sym) :: trs) in
            let abs = PD.abstract srk tr_phi in
            Log.errorf "ABS DONE";
          PD.exp srk trs (mk_const srk lc) abs)
        else
          PD.exp srk trs (mk_const srk lc) (PD.abstract srk tr_phi) 
        in
        let t2 = time "OUT STAR" in
        diff t1 t2 "STAR";
        pre, post,res 
      in
      {mul; add; star; zero; one}
    in
    let wg = WeightedGraph.add_vertex (WeightedGraph.empty alg) start_vert in
    let wg = WeightedGraph.add_vertex wg goal_vert in
    let wg = Relation.Set.fold 
        (fun rel_sym wg -> WeightedGraph.add_vertex wg rel_sym)
        (get_relations_used fp)
        wg
    in
    let wg = 
      List.fold_left
        (fun wg (rel_atoms, phi, conc) ->
           match rel_atoms with
           | [] -> WeightedGraph.add_edge 
                     wg 
                     start_vert
                     (emptyarr, BatArray.of_list (params_of_atom conc), phi)
                     (rel_of_atom conc)
           | [hd] -> 
             Log.errorf "Edge from %n to %n\n" (rel_of_atom hd) (rel_of_atom conc);
             WeightedGraph.add_edge 
               wg 
               (rel_of_atom hd)
               (BatArray.of_list (params_of_atom hd), 
                BatArray.of_list (params_of_atom conc), 
                phi)
               (rel_of_atom conc)
           | _ -> failwith "Rule with multiple relations in hypothesis")
        wg
        fp.rules
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
        fp.queries
    in
    wg

  let check srk fp pd =
    let t1 = time "CHECK IN" in
    if is_linear fp then (
      let wg = to_weighted_graph srk fp pd in
      Log.errorf "FP is\n\n %a" (pp srk) fp;
      assert (1 = 2);

      let pre, post, phi = WeightedGraph.path_weight wg start_vert goal_vert in    
      let filename =  "/Users/jakesilverman/Documents/duet/duet/final_SRK.smt2" in
      let chan = Stdlib.open_out filename in
      let formatter = Format.formatter_of_out_channel chan in
      Formula.pp srk formatter phi;
      Format.pp_print_newline formatter ();
      Stdlib.close_out chan; 
      to_file srk phi "/Users/jakesilverman/Documents/duet/duet/final_phi.smt2";
      let t2 = time "CHECK MID" in
      diff t1 t2 "CHECK MID";
      let trs = [] in
      Log.errorf "trs size is %n" (List.length trs);
      Log.errorf "pre isze is %n post size is %n" (Array.length pre) (Array.length post);



      let tf = TransitionFormula.make phi trs in
      let _, _, tf_proj = Arraycontent.projection srk tf in
      let matrix = Arraycontent.to_mfa srk tf_proj in
      let iter_trs = TransitionFormula.symbols tf_proj in
      Log.errorf "iter_trs size is %n" (List.length iter_trs);
      let lia = Arraycontent.mfa_to_lia srk matrix iter_trs in
      let tlia = time "CHECK LIA" in
      diff t2 tlia "CHECK LIA";
      to_file srk lia "/Users/jakesilverman/Documents/duet/duet/real_final_phi.smt2";
      let ground, _ = Arraycontent.mbp_qe srk lia true in
      to_file srk ground "/Users/jakesilverman/Documents/duet/duet/final_ground.smt2";
      let tground = time "CHECK GROUND" in
      diff tlia tground "CHECK GROUND";
      assert (1 = 2);
      begin match Quantifier.simsat_forward srk lia with
        | `Unsat -> let t3 = time "CHECK END" in diff t1 t3 "CHECK END"; `No
        | `Unknown -> let t3 = time "CHECK END" in diff t1 t3 "CHECK END";`Unknown
        | `Sat -> let t3 = time "CHECK END" in diff t1 t3 "CEHCK END";`Unknown
      end)
    else failwith "No methods for solving non lin fp"

  let solve srk fp pd =
    if is_linear fp then (
      let wg = to_weighted_graph srk fp pd in
      let soln = 
        (fun rel -> 
           let _, params, phi = WeightedGraph.path_weight wg start_vert rel in 
           params, phi) 
      in
      soln)
    else failwith "No methods for solving non lin fp"


end

module ChcSrkZ3 = struct
  
  let typ_of_sort sort =
    let open Z3enums in
    match Z3.Sort.get_sort_kind sort with
    | REAL_SORT -> `TyReal
    | INT_SORT -> `TyInt
    | BOOL_SORT -> `TyBool
    | ARRAY_SORT -> `TyFun ([`TyInt], `TyInt) 
    |_ -> failwith "TODO: allow function types"

  let mk_eq_by_sort srk s1 s2 =
    assert (typ_symbol srk s1 = typ_symbol srk s2);
    match typ_symbol srk s1 with
    | `TyInt | `TyReal -> mk_eq srk (mk_const srk s1) (mk_const srk s2)
    | `TyBool -> mk_iff srk (mk_const srk s1) (mk_const srk s2)
    | `TyFun ([`TyInt], `TyInt) ->
      mk_forall 
        srk 
        ~name:"i" 
        `TyInt 
        (mk_eq 
           srk 
           (mk_app srk s1 [mk_var srk 0 `TyInt])
           (mk_app srk s2 [mk_var srk 0 `TyInt]))  
    | _ -> failwith "Unsupported type in CHC"


  (* Creates a relation atom from a z3 predicate in which each argument
   * to the predicate is an integer. Replaces integer [i] with value
   * located at key [i] in table [ind_to_sym] when such a key exists *)
  let rel_atom_of_z3 srk fp ind_to_sym rsym_to_int names z3pred =
    Log.errorf "FAILED IN HERE";
    let eqs = ref [] in
    let args = List.map 
        (fun arg ->
           begin match Z3.AST.get_ast_kind (Z3.Expr.ast_of_expr arg) with
             | VAR_AST ->
               let index = Z3.Quantifier.get_index arg in
               if BatHashtbl.mem ind_to_sym index then
                 BatHashtbl.find ind_to_sym index
               else (
                 let sort = typ_of_sort (Z3.Expr.get_sort arg) in
                 let sym = 
                   mk_symbol srk ~name:(Z3.Symbol.to_string names.(index)) sort 
                 in
                 BatHashtbl.add ind_to_sym index sym;
                 sym) 
             | NUMERAL_AST ->
               let sym = mk_symbol srk `TyInt in
               eqs := (mk_eq srk (mk_const srk sym) (SrkZ3.term_of_z3 srk arg)) :: !eqs;
               sym
             | APP_AST -> 
               begin match Z3.FuncDecl.get_decl_kind (Z3.Expr.get_func_decl arg) with
               | OP_TRUE ->
                 let sym = mk_symbol srk `TyBool in
                 eqs := (mk_const srk sym) :: !eqs;
                 sym
               | OP_FALSE -> 
                 let sym = mk_symbol srk `TyBool in
                 eqs := (mk_not srk (mk_const srk sym)) :: !eqs;
                 sym
               | _ -> failwith "Complex term as input to rel atom"
               end
             | _ -> assert false
           end) 
        (Z3.Expr.get_args z3pred) in
    let decl = Z3.Expr.get_func_decl z3pred in
    let rsym = Z3.Symbol.to_string (Z3.FuncDecl.get_name decl) in
    let relation = 
      if Hashtbl.mem rsym_to_int rsym then Hashtbl.find rsym_to_int rsym
      else (
        let typ = List.map (fun arg -> typ_symbol srk arg) args in
        let res = mk_relation fp ~name:rsym typ in
        Hashtbl.add rsym_to_int rsym res;
        res)
    in
    (relation, args), !eqs

  (* Similiar to above but always uses creates a fresh symbol. [eq_syms] tracks
   * which fresh symbols we created for indices that already exist in 
   * [ind_to_sym] *)
  let rel_atom_of_z3_fresh srk fp ind_to_sym rsym_to_int names z3pred =
    let fresh_index_map = BatHashtbl.create 91 in
    let eq_syms = ref [] in
    let atom, eqs = 
      rel_atom_of_z3 srk fp fresh_index_map rsym_to_int names z3pred 
    in
    BatHashtbl.iter (fun ind sym ->
        if BatHashtbl.mem ind_to_sym ind 
        then eq_syms := ((BatHashtbl.find ind_to_sym ind), sym) :: !eq_syms
        else BatHashtbl.add ind_to_sym ind sym)
      fresh_index_map;
    atom, eqs, !eq_syms

  let unbooleanize srk (hypo, phi, conc) =
    let syms = symbols phi in
    let bool_syms = Symbol.Set.filter (fun s -> typ_symbol srk s = `TyBool) syms in
    let bsym_to_isym = BatHashtbl.create 91 in
    Symbol.Set.iter (fun e -> BatHashtbl.add bsym_to_isym e (mk_symbol srk `TyInt)) bool_syms;
    let phi = 
      substitute_const 
        srk
        (fun s -> 
           if Hashtbl.mem bsym_to_isym s then
             mk_eq srk (mk_one srk) (mk_const srk (Hashtbl.find bsym_to_isym s))
           else
             mk_const srk s)
        phi
    in
    let booleanize =
      Hashtbl.fold (fun _ i acc -> 
          mk_or 
            srk 
            [mk_eq srk (mk_const srk i) (mk_one srk);
             mk_eq srk (mk_const srk i) (mk_zero srk)] :: acc)
        bsym_to_isym
        []
    in
    let phi = mk_and srk (phi :: booleanize) in
    let hypo = 
      List.map 
        (fun (rel, syms) -> 
           let syms = List.map (fun s -> if Hashtbl.mem bsym_to_isym s 
                                 then Hashtbl.find bsym_to_isym s
                                 else s) 
               syms
           in
           rel, syms)
        hypo
    in
    let (crel, csyms) = conc in
    let csyms =
      List.map (fun s -> if Hashtbl.mem bsym_to_isym s 
                 then Hashtbl.find bsym_to_isym s
                 else s) 
        csyms
    in
    hypo, phi, (crel, csyms)





  let parse_z3fp ?(z3queries=[]) srk fp z3fp =
    let rsym_to_int = BatHashtbl.create 91 in
    let decl_kind e = Z3.FuncDecl.get_decl_kind (Z3.Expr.get_func_decl e) in
    let parse_rule rule =
      Log.errorf "\n\nRule is %s\n" (Z3.Expr.to_string rule);
      let quanted, names, matrix =
        if Z3.AST.is_quantifier (Z3.Expr.ast_of_expr rule) then
          let q = Z3.Quantifier.quantifier_of_expr rule in
          List.combine 
            (List.rev (Z3.Quantifier.get_bound_variable_sorts q))
            (List.rev (Z3.Quantifier.get_bound_variable_names q)),
BatArray.of_list (Z3.Quantifier.get_bound_variable_names q), 
          Z3.Quantifier.get_body q
        else [], BatArray.init 0 (fun _ -> failwith "empty array"), rule
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
                       &&decl_kind arg = OP_UNINTERPRETED)
                    (Z3.Expr.get_args hypo) 
                in
                Log.errorf "AND2";
                let rel_atoms, eqs = 
                  List.split(
                  List.map 
                    (rel_atom_of_z3 srk fp ind_to_sym rsym_to_int names)
                    rels)
                in
                Log.errorf "AND3";
               rel_atoms, List.flatten eqs, z3phis
              | OP_UNINTERPRETED -> 
                let atom, eqs = rel_atom_of_z3 srk fp ind_to_sym rsym_to_int names hypo in
                [atom], eqs, []
              (* Potentially need add special handling for "OR" case similar to
               * "AND" case *)
              | _ -> [], [], [hypo] 
            end
          in
          Log.errorf "OUT OF AND";
          let conc, eqs_args_conc, eq_syms = 
            rel_atom_of_z3_fresh srk fp ind_to_sym rsym_to_int names conc 
          in
          let phi = 
            mk_and 
              srk 
              (List.map (SrkZ3.formula_of_z3 srk ~skolemized_quants:ind_to_sym) z3phis) 
          in
          let eqs = 
            List.map (fun (s, t) -> mk_eq_by_sort srk s t)
              eq_syms
          in
          let phi = mk_and srk (phi :: eqs @ eqs_args @ eqs_args_conc) in
          let r = atoms, phi, conc in
          unbooleanize srk r
        | (OP_UNINTERPRETED, _) ->
          let conc, eqs = 
            rel_atom_of_z3 srk fp ind_to_sym rsym_to_int names matrix 
          in
          let r = [], mk_and srk eqs, conc in
          unbooleanize srk r
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
    assert (1 = 2);
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
