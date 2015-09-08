open OUnit
open Memo

module Fib = Tabulate.MakeRec(
  struct
    type dom = int
    type cod = int
    let f fib x k =
      if x = 0 then k 0
      else if x = 1 then k 1
      else fib (x - 1) (fun x1 -> fib (x - 2) (fun x2 -> k (x1 + x2)))
    let hash x = x
    let join x y = y
    let bottom = 0
    let dom_equal = (=)
    let cod_equal = (=)
  end)

module CycleTest = Tabulate.MakeRec(
  struct
    type dom = int
    type cod = int

    (* Cyclic dependency: f 0 -> f 3 -> f 2 -> f 1 -> f 0 *)
    let f g x k =
      if x = 0 then g 3 (fun r -> if r > 10 then k 10 else k (r + 1))
      else g (x - 1) (fun r -> k (r + 1))
    let hash x = x
    let join = max
    let bottom = 0
    let dom_equal = (=)
    let cod_equal = (=)
  end)

let assert_equal_int = assert_equal ~printer:string_of_int

let test_tab_fib () =
  assert_equal_int (Fib.call_direct 0) 0;
  assert_equal_int (Fib.call_direct 1) 1;
  assert_equal_int (Fib.call_direct 10) 55;
  assert_equal_int (Fib.call_direct 20) 6765

let test_tab_cycle () =
  assert_equal_int (CycleTest.call_direct 0) 10;
  assert_equal_int (CycleTest.call_direct 1) 11;
  assert_equal_int (CycleTest.call_direct 2) 12

let suite = "Memo" >:::
            [
              "Tabulate Fibonnacci" >:: test_tab_fib;
              "Tabulate Cycle" >:: test_tab_cycle;
            ]
