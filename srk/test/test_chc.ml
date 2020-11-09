open Srk
open OUnit
open Syntax
open Test_pervasives
open Chc
open Iteration
module A = Arraycontent

let pd = (module Product(LinearRecurrenceInequation)(PolyhedronGuard) :
  PreDomain)

let ad = (module A.Array_analysis(Product(LinearRecurrenceInequation)(PolyhedronGuard)) : PreDomain)


let mk_rel_atom_fresh srk fp ?(name="R") syms =
  let typs = List.map (typ_symbol srk) syms in
  let rel = mk_relation fp ~name typs in
  mk_rel_atom srk fp rel syms

let mk_n_rel_atoms_fresh srk fp ?(name="R") syms n = 
  BatArray.init n (fun _ -> mk_rel_atom_fresh srk fp ~name syms)

let countup1 () =
  let fp = Fp.create () in
  let r1 = mk_relation fp [`TyInt] in
  let r2 = mk_relation fp [`TyInt] in
  let error = mk_relation fp [] in
  let atom1 = mk_rel_atom srk fp r1 [xsym] in
  let atom2 = mk_rel_atom srk fp r2 [xsym'] in
  let error_atom = mk_rel_atom srk fp error [] in
  let () =
    let open Infix in
    Fp.add_rule fp [atom1] (x' = x + (int 1)) atom2; 
    Fp.add_rule fp [atom2] (x = x' + (int 1)) atom1;
    Fp.add_rule fp [] ((int 0) <= x) atom1;
    Fp.add_rule fp [atom2] (x' <= (int 0)) error_atom;
    Fp.add_query fp error;
  in
  let res = Fp.check srk fp pd in
  assert (res = `No)

let countup2 () =
  let fp = Fp.create () in
  let r1 = mk_relation fp [`TyInt] in
  let r2 = mk_relation fp [`TyInt] in
  let error = mk_relation fp [] in
  let atom1 = mk_rel_atom srk fp r1 [xsym] in
  let atom2 = mk_rel_atom srk fp r2 [xsym'] in
  let error_atom = mk_rel_atom srk fp error [] in
  let () =
    let open Infix in
    Fp.add_rule fp [atom1] (x' = x + (int 1)) atom2;
    Fp.add_rule fp [atom2] (x = x' + (int 1)) atom1; 
    Fp.add_rule fp [] ((int 0) <= x) atom1;
    Fp.add_rule fp [atom2] ((int 0) <= x') error_atom;
    Fp.add_query fp error;
  in
  let res = Fp.check srk fp pd in
  assert (res = `Unknown)

let xskipcount () =
  let fp = Fp.create () in
  let vert = mk_n_rel_atoms_fresh srk fp [xsym; ysym] 3 in
  let map = [(xsym, xsym'); (ysym, ysym')] in
  let postify rel_atom = 
    let syms' = List.map 
        (fun sym -> 
           match BatList.assoc_opt sym map with
           | None -> sym
           | Some sym' -> sym')
        (params_of_atom rel_atom)
    in
    mk_rel_atom srk fp (rel_of_atom rel_atom) syms'
  in
  let () =
    let open Infix in
    Fp.add_rule fp [] (y' = x') (postify vert.(0));
    Fp.add_rule fp [vert.(0)] (x' = x + (int 1) && y' = y) (postify vert.(1));
    Fp.add_rule fp [vert.(0)] (x' = x && y' = y) (postify vert.(1));
    Fp.add_rule fp [vert.(1)] (y' = y + (int 1) && x' = x) (postify vert.(0));
    Fp.add_rule fp [vert.(0)] (y' < x' && x' = x && y' = y) (postify vert.(2));
    Fp.add_query fp (rel_of_atom vert.(2));
  in
  let res = Fp.solve srk fp pd in
  assert_equiv_formula (snd (res (rel_of_atom (vert.(2))))) (mk_false srk)

let dupuncontrsym () =
  let fp = Fp.create () in
  let vert = mk_n_rel_atoms_fresh srk fp [] 2 in
  let () =
    let open Infix in
    Fp.add_rule fp [] (y = (int 1)) vert.(0);
    Fp.add_rule fp [vert.(0)] (y = (int 0)) vert.(1);
  in
  let res = Fp.solve srk fp pd in
  assert_not_implies (snd (res (rel_of_atom vert.(1) ))) (mk_false srk)

let arr_read_write () =
  let smt2str =
     "(declare-rel L ((Array Int Int) Int))
      (declare-rel Entry ((Array Int Int) Int))
      (declare-rel Error ())
      (declare-var i Int)
      (declare-var |i'| Int)
      (declare-var a1 (Array Int Int))
      (declare-var a2 (Array Int Int))
      (rule (=> (= i 0) (Entry a1 i)))
      (rule (=> (and (Entry a1 i) (= a1 a2) (= (select a1 i) 99) (= (+ i 1) |i'|)) (L a2 |i'|)))
     (rule (=> (and (L a1 i) (= (+ i 1) |i'|) (= a1 a2) (= (select a1 i) 99)) (L a2 |i'|)))

     (rule (=> (and (L a1 i) (< 10 i) (= (select a1 5) 1)) Error))

      (query Error)"
  in
  let fp = Chc.Fp.create () in
  Log.errorf "HERE";
  let fp = Chc.ChcSrkZ3.parse_string srk fp smt2str in
  Log.errorf "CHC is %a" (Chc.Fp.pp srk) fp;
  Log.errorf "HERE2";
  let res = Fp.check srk fp ad in
  Log.errorf "FAILEDHERE";
  assert (res = `No)
  
let suite = "Chc" >:::
  [
(*    "countup1" >:: countup1;
    "counterup2" >:: countup2;
    "xskipcount" >:: xskipcount;
    "dupunconstrsym" >:: dupuncontrsym;*)
    "arr_read_write" >:: arr_read_write
  ]
