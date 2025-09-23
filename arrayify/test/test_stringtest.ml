open Arrayify
open Variable 
open Translator
open Symbolicheap

module Heap = Set.Make(HeapElem)


let strlen_test () = (
  print_string "\n\n\nRunning Translation on test/files/c/str-alg-processed/strlen_benchmark.c...\n\n\n";
  let b = new_bvar 0 in 
  let p = new_pvar "%0" in 
  let formula = And (BlockEq (Block (Pointer p), BVar b), Eq (Offset (Pointer p), Int 0)) in 
  let heap = Heap.singleton (Array b) in 
  let sheap = (formula, heap) in
  translate "/Users/np6641/dev/arrayify/test/files/c/str-alg-processed/strlen_benchmark.c" sheap
)  


let () = (
   let _ = strlen_test in
   (* min_test (); *)
   (* comp_test (); *)
   (* basic_test (); *)
   strlen_test ();
)

