open Srk
open Syntax
open OUnit

module C = MakeSimplifyingContext ()
module TF = TransitionFormula
module SF = SkolemFragment

let srk = C.context
let sym name typ = mk_symbol srk ~name typ
let c = mk_const srk
let int = mk_int srk
let eq x y = mk_eq srk x y
let conj = mk_and srk
let neg = mk_not srk
let add a b = mk_add srk [a; b]

(* A transition updates index i and array a. The source array b is either a
   symbolic constant or a Skolem, depending on the test. *)
let i = sym "i" `TyInt
let i_post = sym "i'" `TyInt
let a = sym "a" `TyArr
let a_post = sym "a'" `TyArr
let b = sym "b" `TyArr
let n = sym "n" `TyInt
let fresh = sym "fresh" `TyInt
let pairs = [i, i_post; a, a_post]

(* In formula comments, R denotes TF.formula relation and B denotes
   TF.formula both. The mapped symbols for a and a' are z and z'; q is the
   mapped symbol for b when b is a symbolic constant. The selected index is j.
   Existential quantifiers describe the transition formula's metadata. *)

let read array at = mk_select srk (c array) at
(* i' = i + 1 /\ a' = store(a, i, value). *)
let update value =
  conj [eq (c i_post) (add (c i) (int 1));
        eq (c a_post) (mk_store srk (c a) (c i) value)]

let mapped_symbol correspondence array =
  match SF.mapped_symbol correspondence array with
  | Some value -> value
  | None -> assert_failure "missing mapped integer symbol"

let mapped_value correspondence array = c (mapped_symbol correspondence array)

let check expected phi =
  let solver = SrkZ3.Solver.make srk in
  SrkZ3.Solver.add solver [phi];
  let show = function `Sat -> "sat" | `Unsat -> "unsat" | `Unknown -> "unknown" in
  assert_equal ~printer:show ~msg:(Formula.show srk phi)
    expected (SrkZ3.Solver.check solver)

(* phi entails psi exactly when phi /\ not psi is unsatisfiable. *)
let entails phi psi = check `Unsat (conj [phi; neg psi])

let assert_formula_equal expected actual =
  assert_equal ~cmp:Formula.equal ~printer:(Formula.show srk) expected actual

let copy_symbolic_array () =
  (* i' = i + 1 /\ a' = store(a, i, b[i]). *)
  let original = TF.make (update (read b (c i))) pairs in
  let correspondence, relation = SF.project srk original in
  let j = c (SF.index correspondence) in
  let before = mapped_value correspondence a in
  let after = mapped_value correspondence a_post in
  let source = mapped_symbol correspondence b in
  (* The projected relation entails:
       i' = i + 1
       /\ (j = i -> after = source)
       /\ (j <> i -> after = before),
     where before = a[j], after = a'[j], and source = b[j]. *)
  entails (TF.formula relation)
    (conj [eq (c i_post) (add (c i) (int 1));
           mk_if srk (eq j (c i)) (eq after (c source));
           mk_if srk (neg (eq j (c i))) (eq after before)]);
  (* Check a satisfiable example of each branch so the implications cannot
     pass vacuously. *)
  (* R /\ j = i /\ source = 7 /\ before = 3 /\ after = 7. *)
  check `Sat (conj [TF.formula relation; eq j (c i); eq (c source) (int 7);
                   eq before (int 3); eq after (int 7)]);
  (* R /\ j <> i /\ source = 7 /\ before = 3 /\ after = 3. *)
  check `Sat (conj [TF.formula relation; neg (eq j (c i)); eq (c source) (int 7);
                   eq before (int 3); eq after (int 3)]);
  assert_bool "mapped source stays a symbolic constant"
    (TF.is_symbolic_constant relation source);
  assert_bool "index stays a symbolic constant"
    (TF.is_symbolic_constant relation (SF.index correspondence))

let scalar_skolem_across_steps () =
  (* exists fresh. i' = i + 1 /\ a' = store(a, i, fresh). *)
  let original = TF.make ~exists:(fun s -> s <> fresh) (update (c fresh)) pairs in
  (* R = i' = i + 1 /\ a' = store(a, i, fresh)
         /\ z = a[j] /\ z' = a'[j].
     The arrays and fresh are implicitly existential; j is a symbolic constant. *)
  let correspondence, relation = SF.project srk original in
  assert_bool "scalar Skolem stays existential" (not (TF.exists relation fresh));
  (* Observe index 0. The first iteration writes fresh=3 there; the second
     writes fresh=9 at index 1. Composition must permit these distinct choices. *)
  (* First body: R /\ fresh = 3. *)
  let first = TF.map_formula (fun phi -> conj [phi; eq (c fresh) (int 3)]) relation in
  (* Second body: R /\ fresh = 9. *)
  let second = TF.map_formula (fun phi -> conj [phi; eq (c fresh) (int 9)]) relation in
  let both = TF.mul srk first second in
  (* B /\ i = 0 /\ i' = 2 /\ j = 0 /\ z' = 3. *)
  check `Sat (conj [TF.formula both; eq (c i) (int 0); eq (c i_post) (int 2);
                   eq (c (SF.index correspondence)) (int 0);
                   eq (mapped_value correspondence a_post) (int 3)])

let scalar_constant_across_steps () =
  (* Project i' = i + 1 /\ a' = store(a, i, n), with n constant. *)
  let _, relation = SF.project srk (TF.make (update (c n)) pairs) in
  assert_bool "integer symbolic constant stays constant"
    (TF.is_symbolic_constant relation n);
  (* First body: R /\ n = 3. *)
  let first = TF.map_formula (fun phi -> conj [phi; eq (c n) (int 3)]) relation in
  (* Second body: R /\ n = 9. *)
  let second = TF.map_formula (fun phi -> conj [phi; eq (c n) (int 9)]) relation in
  (* The composition requires n = 3 /\ n = 9, so it is unsatisfiable. *)
  check `Unsat (TF.formula (TF.mul srk first second))

let array_source_across_steps ~symbolic_constant expected () =
  (* Repeatedly overwrite the selected index. A symbolic source array must
     supply the same value there; a Skolem array can be reselected each step. *)
  (* i' = i /\ a' = store(a, i, b[i]). *)
  let body = conj [eq (c i_post) (c i);
                  eq (c a_post) (mk_store srk (c a) (c i) (read b (c i)))] in
  (* If b is a symbolic constant, it stays fixed across steps.
     Otherwise, b is implicitly existential: each step may choose a new array. *)
  let original =
    TF.make ~exists:(fun s -> symbolic_constant || s <> b) body pairs
  in
  let correspondence, relation = SF.project srk original in
  assert_equal ~msg:"only symbolic arrays have a persistent mapped symbol"
    symbolic_constant (SF.mapped_symbol correspondence b <> None);
  (* chosen(value) has body R /\ z' = value. *)
  let chosen value =
    TF.map_formula
      (fun phi -> conj [phi; eq (mapped_value correspondence a_post) (int value)])
      relation
  in
  let both = TF.mul srk (chosen 3) (chosen 9) in
  (* B /\ i = 0 /\ j = 0. The two writes require q = 3 /\ q = 9
     when b is constant; a Skolem b has separate witnesses for the two steps. *)
  check expected (conj [TF.formula both; eq (c i) (int 0);
                        eq (c (SF.index correspondence)) (int 0)])

let skolem_read_consistency () =
  (* Reads from the same Skolem array must agree at equal indices within a
     step, while distinct indices may supply independent values. *)
  (* i' = b[n] /\ a' = store(a, i, b[i]). *)
  let body = conj [eq (c i_post) (read b (c n));
                  eq (c a_post) (mk_store srk (c a) (c i) (read b (c i)))] in
  (* exists b. i' = b[n] /\ a' = store(a, i, b[i]). *)
  let original = TF.make ~exists:(fun s -> s <> b) body pairs in
  let correspondence, relation = SF.project srk original in
  let after = mapped_value correspondence a_post in
  (* at_write = R /\ j = i. *)
  let at_write =
    conj [TF.formula relation; eq (c (SF.index correspondence)) (c i)]
  in
  (* at_write entails i = n -> z' = i', since both values then read b[i]. *)
  entails at_write (mk_if srk (eq (c i) (c n)) (eq after (c i_post)));
  (* at_write /\ i = 0 /\ n = 0 /\ z' = 3 /\ i' = 3. *)
  check `Sat (conj [at_write; eq (c i) (int 0); eq (c n) (int 0);
                   eq after (int 3); eq (c i_post) (int 3)]);
  (* at_write /\ i = 0 /\ n = 1 /\ z' = 3 /\ i' = 9. *)
  check `Sat (conj [at_write; eq (c i) (int 0); eq (c n) (int 1);
                   eq after (int 3); eq (c i_post) (int 9)])

let symbolic_array_off_index () =
  (* For a symbolic array, projection keeps only its selected value fixed.
     Observe index 0, but copy b[1] into a[0]: different steps may use different
     witnesses for b away from index 0. This is deliberate information loss. *)
  (* i' = i /\ a' = store(a, i, b[n]), with b and n symbolic constants. *)
  let body = conj [eq (c i_post) (c i);
                  eq (c a_post) (mk_store srk (c a) (c i) (read b (c n)))] in
  let correspondence, relation = SF.project srk (TF.make body pairs) in
  (* chosen(value) has body R /\ z' = value. *)
  let chosen value =
    TF.map_formula
      (fun phi -> conj [phi; eq (mapped_value correspondence a_post) (int value)])
      relation
  in
  let both = TF.mul srk (chosen 3) (chosen 9) in
  (* B /\ i = 0 /\ n = 1 /\ j = 0 /\ q = 7.
     The shared q fixes b[0] = 7; the two witnesses for b[1] can be 3 and 9. *)
  check `Sat (conj [TF.formula both; eq (c i) (int 0); eq (c n) (int 1);
                   eq (c (SF.index correspondence)) (int 0);
                   eq (mapped_value correspondence b) (int 7)])

let real_scalar_state () =
  let x = sym "x" `TyReal and x_post = sym "x'" `TyReal in
  let delta = sym "delta" `TyReal in
  (* x' = x + delta, with delta a real symbolic constant. *)
  let formula = eq (c x_post) (add (c x) (c delta)) in
  let _, relation = SF.project srk (TF.make formula [x, x_post]) in
  assert_equal [x, x_post] (TF.symbols relation);
  assert_formula_equal formula (TF.formula relation);
  assert_bool "real symbolic constant stays constant"
    (TF.is_symbolic_constant relation delta)

let transition_contract () =
  (* Project i' = i + 1 /\ a' = store(a, i, b[i]). *)
  let correspondence, relation = SF.project srk (TF.make (update (read b (c i))) pairs) in
  assert_equal ~msg:"scalar pairs are preserved and array pairs are mapped"
    [i, i_post;
     mapped_symbol correspondence a, mapped_symbol correspondence a_post]
    (TF.symbols relation);
  List.iter (fun array ->
      assert_bool "original array is implicitly existential"
        (not (TF.exists relation array)))
    [a; a_post; b]

let unconstrained_state () =
  (* A state array need not occur in the body. Its selected values must still
     be available, and an unconstrained transition must not acquire a frame. *)
  (* The original body is true: neither i' nor a' is constrained. *)
  let correspondence, relation = SF.project srk (TF.make (mk_true srk) pairs) in
  (* R /\ z = 3 /\ z' = 9. *)
  check `Sat (conj [TF.formula relation;
                   eq (mapped_value correspondence a) (int 3);
                   eq (mapped_value correspondence a_post) (int 9)]);
  (* Project the identity i' = i /\ a' = a. *)
  let identity, relation = SF.project srk (TF.identity srk pairs) in
  (* R entails z = z'. *)
  entails (TF.formula relation)
    (eq (mapped_value identity a) (mapped_value identity a_post))

let scalar_only () =
  (* 0 <= i /\ i < n /\ i' = i + fresh. *)
  let formula = conj [mk_leq srk (int 0) (c i);
                      mk_lt srk (c i) (c n);
                      eq (c i_post) (add (c i) (c fresh))] in
  (* exists fresh. 0 <= i /\ i < n /\ i' = i + fresh. *)
  let original = TF.make ~exists:(fun s -> s <> fresh) formula [i, i_post] in
  let correspondence, relation = SF.project srk original in
  assert_formula_equal formula (TF.formula relation);
  assert_bool "scalar symbolic constant stays constant"
    (TF.is_symbolic_constant relation n);
  assert_bool "scalar Skolem stays existential" (not (TF.exists relation fresh));
  List.iter (fun symbol ->
      assert_equal None (SF.mapped_symbol correspondence symbol))
    [i; n; fresh]

let lift_binders () =
  (* i' = i + 1 /\ a' = store(a, i, b[i]) /\ i <= n. *)
  let original =
    TF.make (conj [update (read b (c i)); mk_leq srk (c i) (c n)]) pairs
  in
  let correspondence, _ = SF.project srk original in
  (* sum = z + q + n. *)
  let sum = mk_add srk [mapped_value correspondence a;
                        mapped_value correspondence b; c n] in
  (* Lift pre-state, post-state, and constant symbols beneath a binder.
     The unrelated scalar symbol n must remain free. *)
  (* forall k. k = j -> z' = z + q + n. *)
  let scalar = mk_forall srk `TyInt
      (mk_if srk (eq (mk_var srk 0 `TyInt) (c (SF.index correspondence)))
         (eq (mapped_value correspondence a_post) sum)) in
  (* forall j. forall k. k = j -> a'[j] = a[j] + b[j] + n. *)
  let lifted = SF.lift srk correspondence scalar in
  let j = mk_var srk 0 `TyInt in
  (* forall j. a'[j] = a[j] + b[j] + n. *)
  let expected = mk_forall srk `TyInt
      (eq (read a_post j) (mk_add srk [read a j; read b j; c n])) in
  (* Check both directions of the equivalence between these formulas. *)
  entails lifted expected;
  entails expected lifted

let suite = "SkolemFragment" >::: [
    "copy from symbolic array" >:: copy_symbolic_array;
    "scalar Skolem across steps" >:: scalar_skolem_across_steps;
    "scalar symbolic constant across steps" >:: scalar_constant_across_steps;
    "array symbolic constant across steps" >::
      array_source_across_steps ~symbolic_constant:true `Unsat;
    "array Skolem across steps" >::
      array_source_across_steps ~symbolic_constant:false `Sat;
    "Skolem array read consistency" >:: skolem_read_consistency;
    "symbolic array retains only selected value" >:: symbolic_array_off_index;
    "real scalar state preserved" >:: real_scalar_state;
    "transition formula contract" >:: transition_contract;
    "unconstrained and identity state" >:: unconstrained_state;
    "scalar-only formula preserved" >:: scalar_only;
    "lifting avoids capture" >:: lift_binders;
  ]
