open Srk
open OUnit
open Syntax
open Test_pervasives
open Chc
open Iteration

let rel_ctx = mk_relcontext

let pd = (module Product(LinearRecurrenceInequation)(PolyhedronGuard) :
  PreDomain)


let countup1 () =
  let r1 = mk_relation rel_ctx [`TyInt] in
  let r2 = mk_relation rel_ctx [`TyInt] in
  let error = mk_relation rel_ctx [] in
  let atom1 = mk_rel_atom srk rel_ctx r1 [xsym] in
  let atom2 = mk_rel_atom srk rel_ctx r2 [xsym'] in
  let error_atom = mk_rel_atom srk rel_ctx error [] in
  let hypo1 =  mk_hypo [atom1] (mk_eq srk x' (mk_add srk [mk_one srk; x])) in
  let rule1 = mk_rule hypo1 atom2 in
  let hypo2 = mk_hypo [atom2] (mk_eq srk x (mk_add srk [mk_one srk; x'])) in
  let rule2 = mk_rule hypo2 atom1 in
  let rule3 = mk_fact (mk_leq srk (mk_zero srk) x) atom1 in
  let error_hypo = mk_hypo [atom2] (mk_leq srk x' (mk_zero srk)) in
  let rule4 = mk_rule error_hypo error_atom in
  let query = error in
  let chc = Chc.chc_of [rule1; rule2; rule3; rule4] [query] in
  let res = Chc.has_reachable_goal srk chc pd in
  assert (res = `No)

let countup2 () =
  let r1 = mk_relation rel_ctx [`TyInt] in
  let r2 = mk_relation rel_ctx [`TyInt] in
  let error = mk_relation rel_ctx [] in
  let atom1 = mk_rel_atom srk rel_ctx r1 [xsym] in
  let atom2 = mk_rel_atom srk rel_ctx r2 [xsym'] in
  let error_atom = mk_rel_atom srk rel_ctx error [] in
  let hypo1 =  mk_hypo [atom1] (mk_eq srk x' (mk_add srk [mk_one srk; x])) in
  let rule1 = mk_rule hypo1 atom2 in
  let hypo2 =  mk_hypo [atom2] (mk_eq srk x (mk_add srk [mk_one srk; x'])) in
  let rule2 = mk_rule hypo2 atom1 in
  let rule3 = mk_fact (mk_leq srk (mk_zero srk) x) atom1 in
  let error_hypo = mk_hypo [atom2] (mk_leq srk (mk_zero srk) x') in
  let rule4 = mk_rule error_hypo error_atom in
  let query = error in
  let chc = Chc.chc_of [rule1; rule2; rule3; rule4] [query] in
  let res = Chc.has_reachable_goal srk chc pd in
  assert (res = `Unknown)

let xskipcount () =
  let vert = mk_n_rel_atoms_fresh srk rel_ctx [xsym; ysym] 3 in
  let map = [(xsym, xsym'); (ysym, ysym')] in
  let edge0 = 
    mk_mapped_rule 
      map 
      [] 
      (mk_eq srk y' x')
      vert.(0)
  in
  let edge1 = 
    mk_mapped_rule
      map
      [vert.(0)]
      (mk_and 
         srk 
         [(mk_eq srk x' (mk_add srk [x; mk_one srk]));
          mk_eq srk y y'])
      vert.(1)
  in 
  let edge2 = 
    mk_mapped_rule
      map
      [vert.(0)]
      (mk_eq_syms srk map)
      vert.(1)
  in 
  let edge3 = 
    mk_mapped_rule
      map
      [vert.(1)]
      (mk_and 
         srk 
         [(mk_eq srk y' (mk_add srk [y; mk_one srk]));
          mk_eq srk x x'])
         vert.(0)
  in
  let edge4 =
    mk_mapped_rule
      map
      [vert.(0)]
      (mk_and srk [mk_lt srk y' x'; mk_eq_syms srk map])
      vert.(2)
  in
  let chc = 
    Chc.chc_of 
      [edge0; edge1; edge2; edge3; edge4] 
      [rel_of_atom vert.(2)] 
  in
  let res = Chc.solve srk chc pd in
  assert_equiv_formula (res (rel_of_atom (vert.(2)))) (mk_false srk)





let suite = "Chc" >:::
  [
    "countup1" >:: countup1;
    "counterup2" >:: countup2;
    "xskipcount" >:: xskipcount
  ]
