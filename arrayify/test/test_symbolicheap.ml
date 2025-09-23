open Arrayify
open Symbolicheap
open Variable
module Heap = Set.Make(HeapElem)



let equality_test () = (
  let b = new_bvar 0 in
  let p = new_pvar "p" in
  let x = new_var "x" in
  let formula = And ((Eq (Var x, Int 2), And (BlockEq (Block (Pointer p), BVar b), Eq (Offset (Pointer p), Int 7)))) in
  let heap = Heap.singleton (Array b) in
  let sheap = formula, heap in 

  let formula' = And (Eq ((Var x), (Add (Int 1, Int 1))), And (BlockEq ((Block (Pointer p), BVar b)), Eq (Offset (Pointer p), (Add ((Int 3), (Int 4)))))) in
  let sheap' = formula', heap in 

  assert (sheap_equals sheap sheap')
)

let implication_test () = (
  let b0 = new_bvar 0 in
  let b1 = new_bvar 1 in
  let b2 = new_bvar 2 in
  let p1 = new_pvar "p1" in
  let p2 = new_pvar "p2" in

  let formula = And (BlockEq (Block (Pointer p1), BVar b0), Or (BlockEq (Block (Pointer p2), (BVar b1)), BlockEq ((BVar b2), (Block (Pointer p2))))) in 
  let heap = Heap.singleton (Array b0) in
  let heap = Heap.add (Array b1) heap in
  let sheap = formula, heap in

  assert (sheap_single_b sheap p1 = Some b0);
  assert (sheap_single_b sheap p2 = None)
)

let () = (
  equality_test (); 
  implication_test (); 
  ()
)