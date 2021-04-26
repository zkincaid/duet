open Srk
open OUnit
open Syntax
open Test_pervasives
open Chc
open Iteration

let pd = (module QLIALift(Product(LinearRecurrenceInequation)(PolyhedronGuard)) :
  PreDomain)

let typ_symbol_fo srk sym =
  match typ_symbol srk sym with
  | `TyInt -> `TyInt
  | `TyReal -> `TyReal
  | `TyBool -> `TyBool
  | _ -> assert false

let mk_rel_atom_fresh srk fp ?(name="R") syms =
  let typs = List.map (typ_symbol_fo srk) syms in
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

let countupsuplin () =
  let fp = Fp.create () in
  let r1 = mk_relation fp ~name:"R1" [`TyInt] in
  let r2 = mk_relation fp ~name:"R2" [`TyInt] in
  let r3 = mk_relation fp ~name:"R3" [`TyInt] in
 
  let error = mk_relation fp [] in
  let atom1 = mk_rel_atom srk fp r1 [xsym] in
  let atom2 = mk_rel_atom srk fp r2 [xsym'] in
  let atom3 = mk_rel_atom srk fp r3 [xsym'] in
  let error_atom = mk_rel_atom srk fp error [] in
  let () =
    let open Infix in
    Fp.add_rule fp [] (mk_true srk) atom3;
    Fp.add_rule fp [atom1; atom3] (x' = x + (int 1)) atom2; 
    Fp.add_rule fp [atom2] (x = x' + (int 1)) atom1;
    Fp.add_rule fp [] ((int 0) <= x) atom1;
    Fp.add_rule fp [atom2] (x' <= (int 0)) error_atom;
    Fp.add_query fp error;
  in
  let res = Fp.check srk fp pd in
  assert (res = `No)

let failure_suplin () =
  let fp = Fp.create () in
  let r1 = mk_relation fp ~name:"R1" [`TyInt] in
  let r2 = mk_relation fp ~name:"R2" [`TyInt] in
  let r3 = mk_relation fp ~name:"R3" [`TyInt] in
 
  let error = mk_relation fp [] in
  let atom1 = mk_rel_atom srk fp r1 [xsym] in
  let atom2 = mk_rel_atom srk fp r2 [xsym'] in
  let atom3 = mk_rel_atom srk fp r3 [xsym'] in
  let error_atom = mk_rel_atom srk fp error [] in
  let () =
    let open Infix in
    Fp.add_rule fp [] (mk_true srk) atom3;
    Fp.add_rule fp [atom1; atom3] (x' = x + (int 1)) atom2; 
    Fp.add_rule fp [atom2] (x = x' + (int 1)) atom1;
    Fp.add_rule fp [] ((int 0) <= x) atom1;
    Fp.add_rule fp [atom2] (x' <= (int 0)) error_atom;
    Fp.add_rule fp [atom1] (mk_true srk) atom3;
    Fp.add_query fp error;
  in
  Fp.check srk fp pd

let unbooleanize () =
  let fp = Fp.create () in
  let r1 = mk_relation fp [`TyInt; `TyBool] in
  let r2 = mk_relation fp [`TyInt] in
  let error = mk_relation fp [] in
  let atom1 = mk_rel_atom srk fp r1 [xsym; bsym] in
  let atom2 = mk_rel_atom srk fp r2 [xsym'] in
  let error_atom = mk_rel_atom srk fp error [] in
  let () =
    let open Infix in
    Fp.add_rule fp [atom1] (x' = x + (int 1) && b) atom2; 
    Fp.add_rule fp [atom2] (x = x' + (int 1) && b) atom1;
    Fp.add_rule fp [] ((int 0) <= x && b) atom1;
    Fp.add_rule fp [atom2] (x' <= (int 0)) error_atom;
    Fp.add_query fp error;
  in
  let (_, fp') = Fp.unbooleanize srk fp in
  let res = Fp.check srk fp' pd in
  assert (res = `No)

let failure_unbooleanize () =
  let fp = Fp.create () in
  let r1 = mk_relation fp [`TyInt; `TyBool] in
  let r2 = mk_relation fp [`TyInt] in
  let error = mk_relation fp [] in
  let atom1 = mk_rel_atom srk fp r1 [xsym; bsym] in
  let atom2 = mk_rel_atom srk fp r2 [xsym'] in
  let error_atom = mk_rel_atom srk fp error [] in
  let () =
    let open Infix in
    Fp.add_rule fp [atom1] (x' = x + (int 1) && b) atom2; 
    Fp.add_rule fp [atom2] (x = x' + (int 1) && b) atom1;
    Fp.add_rule fp [] ((int 0) <= x && b) atom1;
    Fp.add_rule fp [atom2] (x' <= (int 0)) error_atom;
    Fp.add_query fp error;
  in
  let res = Fp.check srk fp pd in
  assert (res = `No)

let suite = "Chc" >:::
  [

    "countup1" >:: countup1;
    "counterup2" >:: countup2;
    "xskipcount" >:: xskipcount;
    "dupunconstrsym" >:: dupuncontrsym;
    "countupsuplin" >:: countupsuplin;
    "failure_suplin" >:: (fun _ -> 
        assert_raises 
          (Failure "No methods for solving non super linear chc systems") 
          failure_suplin);
    "unbooleanize" >:: unbooleanize;
    "failure_unbooleanize" >:: (fun _ -> 
        assert_raises 
          (Invalid_argument "SrkApon: environment symbols must be number-typed") 
          failure_unbooleanize);
  ]
