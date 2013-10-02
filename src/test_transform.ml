(*pp camlp4find deriving.syntax *)

open Apak
open OUnit


module StrVar = Test_formula.StrVar

module K = Transition.Make(StrVar)

module V = struct
  type t = int deriving (Compare)
  let equal = (=)
  let compare = Pervasives.compare
  let hash x = x
end

type cmd =
| Assign of StrVar.t * K.T.t
| Assume of K.F.t
    deriving (Show,Compare)
module CmdSyntax = struct
  let ( := ) x y = Assign (x, y)
  let ( ?! ) x = Assume x
  include K.T.Syntax
  include K.F.Syntax
end

module E = struct
  type t = cmd deriving (Show,Compare)
  let default = Assume K.F.top
  let compare = Compare_t.compare
end
module G = Graph.Persistent.Digraph.ConcreteLabeled(V)(E)
module A = Pathexp.MakeElim(G)(K)

let var v = K.T.var (K.V.mk_var v)
let const k = K.T.int (Numeral.ZZ.of_int k)

let weight e =
  let open K in
  match G.E.label e with
  | Assign (v, t) -> K.assign v t
  | Assume phi -> K.assume phi

let run_test graph src tgt =
  let res = A.path_expr graph weight src tgt in
  let s = new Smt.solver in
  Log.logf Log.info "Formula: %a" K.format res;
  s#assrt (K.to_smt res);
  fun phi expected -> begin
    s#push ();
(*    Log.logf Log.info "phi: %a" K.F.format phi;*)
    s#assrt (Smt.mk_not phi);
(*    Log.logf Log.info "solver: %s" (s#to_string ());*)
(*

    if s#check() == Smt.Sat
    then begin let m = s#get_model () in print_endline (m#to_string ()) end;
    assert_equal ~printer:Show.show<Smt.lbool> expected (s#check());
*)
    s#pop ();
  end

(*
let run_test2 graph src tgt =
  let res = A.path_expr graph weight src tgt in
  let s = new Smt.solver in
  Log.logf Log.info "Formula: %a" K.format res;
  print_endline "-------";
  s#assrt (K.to_smt res);
  fun phi expected -> begin
    s#push ();
    begin match res with
    | K.Nonzero res ->
      Log.logf Log.info "phi: %a"
	Show.format<K.F.t Hashcons.hash_consed> (K.F.subst (K.K.mk_subst res) phi);
      s#assrt (Smt.mk_not (K.F.to_smt (K.F.subst (K.K.mk_subst res) phi)));
    | K.Zero -> ()
    end;
    print_endline "-----";
    assert_equal ~printer:Show.show<Smt.lbool> expected (s#check());
    s#pop ();
  end
*)

let mk_graph edges =
  let add_edge g (src, label, tgt) =
    G.add_edge_e g (G.E.create src label tgt)
  in
  List.fold_left add_edge G.empty edges
    
let counter =
  let edges =
    [(0, Assume (K.F.gt (var "n") (const 0)), 1);       (* [n > 0] *)
     (1, Assign ("i", const 0), 2);                     (* i := 0 *)
     (2, Assume (K.F.lt (var "i") (var "n")), 3);       (* [i < n] *)
     (3, Assign ("i", K.T.add (var "i") (const 1)), 2); (* i := i + 1 *)
     (2, Assume (K.F.geq (var "i") (var "n")), 4)]      (* [i >= n] *)
  in
  mk_graph edges
let test_counter () =
  let phi = (Smt.mk_eq (StrVar.to_smt "i'") (StrVar.to_smt "n")) in
  run_test counter 0 4 phi Smt.Unsat

(* from sv-comp13/loops/count_up_down_safe *)
let count_up_down_safe =
  let open CmdSyntax in
  let (~@) x = ~@ (Numeral.QQ.of_int x) in
  let x = var "x" in
  let y = var "y" in
  let n = var "n" in
  let edges =
    [(0, (?! (n >= (~@ 0))), 1); (* nondet uint *)
     (1, ("x" := n), 2);
     (2, ("y" := (~@ 0)), 3);
     (3, (?! (x > (~@ 0))), 4);
     (4, ("x" := x - (~@ 1)), 5);
     (5, ("y" := y + (~@ 1)), 3);
     (3, (?! (x <= (~@ 0))), 6)]
  in
  mk_graph edges
let test_count_up_down_safe () =
  let phi = Smt.mk_eq (StrVar.to_smt "y'") (StrVar.to_smt "n") in
  run_test count_up_down_safe 0 6 phi Smt.Unsat

(* from sv-comp13/loops/sum01_safe *)
let sum01_safe =
  let open CmdSyntax in
  let (~@) x = ~@ (Numeral.QQ.of_int x) in
  let a = ~@ 2 in
  let sn = var "sn" in
  let n = var "n" in
  let i = var "i" in
  let edges =
    [(0, ("i" := (~@ 1)), 1);
     (1, ("sn" := (~@ 0)), 2);
     (2, (?! (i <= n)), 3);
     (3, ("sn" := (sn + a)), 4);
     (4, ("i" := (i + (~@ 1))), 2);
     (2, (?! (i > n)), 5)]
  in
  mk_graph edges
let test_sum01_safe () =
  let open Smt.Syntax in
  let phi =
    (~$ "sn'") == ((~$ "n") * (~@ 2))
    || (~$ "sn'") == (~@ 0)
  in
  run_test sum01_safe 0 5 phi Smt.Unsat

(* from sv-comp13/loops/sum01_unsafe *)
let sum01_unsafe =
  let open CmdSyntax in
  let (~@) x = ~@ (Numeral.QQ.of_int x) in
  let a = ~@ 2 in
  let sn = var "sn" in
  let n = var "n" in
  let i = var "i" in
  let edges =
    [(0, ("i" := (~@ 1)), 1);
     (1, ("sn" := (~@ 0)), 2);
     (2, (?! (i <= n)), 3);

     (3, (?! (i < (~@ 10))), 10);
     (10, ("sn" := (sn + a)), 4);

     (3, (?! (i >= (~@ 10))), 4);

     (4, ("i" := (i + (~@ 1))), 2);
     (2, (?! (i > n)), 5)]
  in
  mk_graph edges
let test_sum01_unsafe () =
  let open Smt.Syntax in
  let phi =
    (~$ "sn'") == ((~$ "n") * (~@ 2))
    || (~$ "sn'") == (~@ 0)
  in
  run_test sum01_unsafe 0 5 phi Smt.Sat

(* from sv-comp13/loops/sum02_safe *)
let sum02_safe =
  let open CmdSyntax in
  let (~@) x = ~@ (Numeral.QQ.of_int x) in
  let sn = var "sn" in
  let n = var "n" in
  let i = var "i" in
  let edges =
    [(0, ("i" := (~@ 0)),1);
     (1, ("sn" := (~@ 0)), 2);
     (2, (?! (i <= n)), 3);
     (3, ("sn" := (sn + i)), 4);
     (4, ("i" := (i + (~@ 1))), 2);
     (2, (?! (i > n)), 5)]
  in
  mk_graph edges
let test_sum02_safe () =
  let open Smt.Syntax in
  let sn = ~$ "sn'" in
  let n = ~$ "n" in
  let i = ~$ "i'" in

  let phi =
    (sn == (((n * n) / (~@ 2)) + (n / (~@ 2)))) || i == (~@ 0)
  in

(*
  let phi =
    i == (~@ 6)
  in

  let phi =
    n == (~@ 5)
  in
*)
(*
  let phi =
    (sn == (n + (((n * n) - n) / (~@ 2)))) || i == (~@ 0)
  in

*)
(*
  let phi =
    (sn == (~@ 10))
  in

*)
  run_test sum02_safe 0 5 phi Smt.Unsat


(* from sv-comp13/loops/sum03_safe *)
let sum03_safe =
  let open CmdSyntax in
  let (~@) x = ~@ (Numeral.QQ.of_int x) in
  let sn = var "sn" in
  let a = ~@ 2 in
  let x = var "x" in
  let edges =
    [(0, ("sn" := (~@ 0)), 1);
     (1, ("x" := (~@ 0)), 2);
     (2, ("sn" := sn + a), 3);
     (3, ("x" := x + (~@ 1)), 4);
     (4, (?! (a == a)), 2)]
  in
  mk_graph edges
let test_sum03_safe () =
  let open Smt.Syntax in
  let phi =
    (~$ "sn'") == ((~$ "x'") * (~@ 2))
  (* this disjunt appears in sum03_safe, but isn't needed *)
  (*    || (~$ "sn'") == (~@ 0)*)
  in
  run_test sum03_safe 0 4 phi Smt.Unsat

(* from sv-comp13/loops/sum03_unsafe *)
let sum03_unsafe =
  let open CmdSyntax in
  let (~@) x = ~@ (Numeral.QQ.of_int x) in
  let sn = var "sn" in
  let a = ~@ 2 in
  let x = var "x" in
  let edges =
    [(0, ("sn" := (~@ 0)), 1);
     (1, ("x" := (~@ 0)), 2);

     (2, (?! (x < (~@ 10))), 3);
     (3, ("sn" := sn + a), 4);

     (2, (?! (x >= (~@ 10))), 4);

     (4, ("x" := x + (~@ 1)), 5);
     (5, (?! (a == a)), 2)]
  in
  mk_graph edges
let test_sum03_unsafe () =
  let open Smt.Syntax in
  let phi =
    (~$ "sn'") == ((~$ "x'") * (~@ 2))
    || (~$ "sn'") == (~@ 0)
  in
  run_test sum03_unsafe 0 5 phi Smt.Sat

let third_order_safe =
  let open CmdSyntax in
  let (~@) x = ~@ (Numeral.QQ.of_int x) in
  let sn = var "sn" in
  let ssn = var "ssn" in
  let n = var "n" in
  let i = var "i" in
  let edges =
    [(0, ("i" := (~@ 0)), 1);
     (1, ("sn" := (~@ 0)), 2);
     (2, ("ssn" := (~@ 0)), 3);
     (3, (?! (i <= n)), 4);
     (5, ("ssn" := (ssn + sn)), 6);
     (4, ("sn" := (sn + i)), 5);
     (6, ("i" := (i + (~@ 1))), 3);
     (3, (?! (i > n)), 7)]
  in
  mk_graph edges
let test_third_order_safe () =
  let open Smt.Syntax in
  let phi =
    (~$ "ssn'") == (((~$ "n") / (~@ 3))
		    + (((~$ "n")*(~$ "n")) / (~@ 2))
		    + (((~$ "n")*(~$ "n")*(~$ "n")) / (~@ 6)))
    || (~$ "ssn'") == (~@ 0)
  in
  run_test third_order_safe 0 7 phi Smt.Unsat

let suite = "Induction" >:::
  [
    "counter" >:: test_counter;
    "count_up_down_safe" >:: test_count_up_down_safe;
    "sum01_safe" >:: test_sum01_safe;
    "sum01_unsafe" >:: test_sum01_unsafe;
    "sum02_safe" >:: test_sum02_safe;
    (* sum02_unsafe does not exist *)
    "sum03_safe" >:: test_sum03_safe;
    "sum03_unsafe" >:: test_sum03_unsafe;
    (* sum04_safe is boring *)
(*    "third_order_safe" >:: test_third_order_safe;*)
  ]
