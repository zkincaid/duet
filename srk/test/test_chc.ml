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

let sup_lin1 () = 
  let fp = Fp.create () in
  let vert = mk_n_rel_atoms_fresh srk fp [xsym] 3 in
  let () =
    let open Infix in
    Fp.add_rule fp [] (x <= (int 10)) (vert.(0));
    Fp.add_rule fp [] ((int 0) <= x) (vert.(1));
    Fp.add_rule fp [vert.(0); vert.(1)] tru (vert.(2));
  in
  let syms,phi = (Fp.solve_super_lin srk fp pd) (rel_of_atom (vert.(2))) in
  let phi' = 
    substitute_const srk (fun sym -> if sym = syms.(0) then x else assert false) phi 
  in
  let psi =
    let open Infix in
    (int 0) <= x && x <= (int 10)
  in
  Log.errorf "PHI IS %a" (Formula.pp srk) phi';
  assert_equiv_formula phi' psi





let test_init () =
  let fp = Chc.Fp.create () in
  let fp = Chc.ChcSrkZ3.parse_file srk fp "/Users/jakesilverman/Documents/arraycopy2.smt2" in
  Log.errorf "Fp is %a" (Chc.Fp.pp srk) fp;
  let res = Fp.check srk fp ad in
  (if res = `No then Log.errorf "RES IS NO" else if
    res = `Unknown then Log.errorf "RES IS UKNNOWN" else
     Log.errorf "RES IS YES");
  assert (res = `No)



let rec rewrite_subst_exists srk eqs (phi : 'a formula) : 'a formula = 
  let unfil_candidates = 
    List.map (fun (t1, t2) -> 
        match Term.destruct srk t1, Term.destruct srk t2 with
        | `Var (ind, _), `Var (ind2, _) ->
          if not (ind = ind2)
          then (Log.errorf "YES"; Some (ind, t2))
          else None
        | `Var(ind, _), _ ->
          Log.errorf "WJHYWHY";
          if not (Hashtbl.mem (free_vars t2) ind)
          then Some (ind, t2)
          else None
        | _, `Var(ind, _) ->
          Log.errorf "EMPEMP";
          if not (Hashtbl.mem (free_vars t1) ind)
          then Some (ind, t1)
          else None
        | _, _ -> (Log.errorf "WTF"; None)) eqs
  in
  let filtered_candidates = 
    List.filter (fun cand ->
        match cand with
        | Some _ -> true
        | None -> false) 
      unfil_candidates
  in
  if List.length filtered_candidates = 0 then phi
  else (
    let (sym, term) = Option.get (List.hd filtered_candidates) in
    let subst = 
      substitute 
        srk
        (fun s -> if s = sym then term else mk_var srk s `TyInt)
    in
    let eqs' = List.map (fun (t1, t2) -> subst t1, subst t2) eqs in
    rewrite_subst_exists srk eqs'
      (substitute srk (fun s -> if s = sym then term else mk_var srk s `TyInt) phi) 
  )

   
let naive_rewrite_elim srk phi =
  let intersect _ = [] in
  let union lsts = List.flatten lsts in
  let alg = function
    | `Tru -> ([], [], mk_true srk)
    | `Fls -> ([], [], mk_false srk)
    | `Atom (`Eq, x, y) -> ([(x, y)], [], mk_eq srk x y)
    | `Atom (`Lt, x, y) -> ([], [], mk_lt srk x y)
    | `Atom (`Leq, x, y) -> ([], [], mk_leq srk x y)
    | `And conjuncts ->
      let (eqs, diseqs, conjs) = 
        List.fold_left (fun (eqs, diseqs, conjs) (eq, diseq, conj) ->
            eq :: eqs, diseq :: diseqs, conj :: conjs)
          ([], [], [])
          conjuncts
      in
      union eqs, intersect diseqs, mk_and srk conjs
    | `Or disjuncts ->
       let (eqs, diseqs, disjs) = 
        List.fold_left (fun (eqs, diseqs, disjs) (eq, diseq, disj) ->
            eq :: eqs, diseq :: diseqs, disj :: disjs)
          ([], [], [])
          disjuncts
      in
      intersect eqs, union diseqs, mk_or srk disjs
    | `Quantify (`Exists, name, typ, (eqs, _, phi)) ->
      Log.errorf "\nPHI HERE IS %a\n" (Formula.pp srk) phi;
      Log.errorf "AT EXISTS FOR %s" name;
List.iter (fun (term1, term2) -> Log.errorf "\nOne eq is %a TO %a"
                      (Term.pp srk) term1 (Term.pp srk) term2) eqs;
    Log.errorf "\n PHI AFTER IS %a\n" (Formula.pp srk) (rewrite_subst_exists srk eqs phi);
      [], [], mk_exists srk ~name typ (rewrite_subst_exists srk eqs phi)
    | `Quantify (`Forall, name, typ, (eqs,diseqs, phi)) ->
      eqs ,diseqs ,mk_forall srk ~name typ phi
    | `Not (eqs, diseqs, phi) -> (diseqs, eqs, mk_not srk phi)
    | `Proposition (`Var _) -> assert false
    | `Proposition (`App (_, _)) -> assert false
    | `Ite ((eq1, diseq1, cond), (eq2, diseq2, bthen), (eq3, diseq3, belse)) -> 
      eq1 @ eq2 @ eq3, diseq1 @ diseq2 @ diseq3, mk_ite srk cond bthen belse
    | _ -> assert false
  in
  Formula.eval srk alg phi


let test_rewrite () =
  let phi = 
    mk_exists_const srk a1sym 
      (mk_exists_const srk a2sym (
        (mk_eq srk a1 a2)))
  in
  Log.errorf "\n\nPHI REWRITE is %a" (Formula.pp srk) phi;
  let _, _, phi = naive_rewrite_elim srk phi in
  Log.errorf "new phi is %a" (Formula.pp srk) phi;
  assert false
 

(*let test_subs ()  =
  let phi =
    let open Infix in
    (exists `TyInt ((forall `TyInt (a (var 1 `TyInt) = (int 99)))))
  in
  let subst =
    substitute_sym 
      srk
      (fun sym ->
         if sym = xsym then x else
           mk_app 
             srk
             sym
             [(mk_var srk 1 `TyInt)])
      phi
  in
  Log.errorf "subst is %a" (Formula.pp srk) subst;
  assert (1 = 2)
*)

  let suite = "Chc" >:::
              [
(*    "countup1" >:: countup1;
    "counterup2" >:: countup2;
    "xskipcount" >:: xskipcount;
    "dupunconstrsym" >:: dupuncontrsym;*)
    (*"arr_read_write" >:: arr_read_write*)
                "sup_lin1" >:: sup_lin1;
               "test_init" >:: test_init;
    (*"test_subs" >:: test_subs*)
    (*"test_rewrite" >:: test_rewrite*)
  ]
