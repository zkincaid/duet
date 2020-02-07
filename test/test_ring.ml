open Srk
open OUnit
open Ring

module UPZ = MakeUltPeriodicSeq(struct
    type t = int
    let add = ( + )
    let mul = ( * )
    let zero = 0
    let one = 1
    let equal = ( = )
    let negate x = -x
  end)

let test_ups_eq () =
  let seq1 =
    UPZ.make [] [1; 2; 3]
  in
  let seq2 =
    UPZ.make [1] [2; 3; 1]
  in
  let seq3 =
    UPZ.make [] [1; 2; 3; 1; 2; 3]
  in
  assert_bool "Equality failure" (UPZ.equal seq1 seq2);
  assert_bool "Equality failure" (UPZ.equal seq1 seq3);
  assert_bool "Equality failure" (UPZ.equal seq3 seq2)

let test_ups_enum () =
  let seq = UPZ.make [1; 2] [3; 4; 5] in
  assert_equal [1;2;3;4;5;3;4;5;3;4] (BatList.of_enum (BatEnum.take 10 (UPZ.enum seq)))
  
let test_ups_add () =
  let seq1 = UPZ.make [1; 2] [3; 4] in
  let seq2 = UPZ.make [1] [2; 3; 4] in
  assert_equal ~cmp:UPZ.equal
    ~printer:(SrkUtil.mk_show (UPZ.pp Format.pp_print_int))
    seq1
    (UPZ.add seq1 UPZ.zero);
  assert_equal ~cmp:UPZ.equal
    ~printer:(SrkUtil.mk_show (UPZ.pp Format.pp_print_int))
    (UPZ.make [2; 4] [6; 8; 5; 7; 7; 6])
    (UPZ.add seq1 seq2);
  assert_equal ~cmp:UPZ.equal
    ~printer:(SrkUtil.mk_show (UPZ.pp Format.pp_print_int))
    UPZ.zero
    (UPZ.add
       (UPZ.add seq1 seq2)
       (UPZ.add (UPZ.negate seq2) (UPZ.negate seq1)))
      
let test_ups_mul () =
  let seq1 = UPZ.make [1] [2; 3] in
  let seq2 = UPZ.make [] [1; 2; 3] in
  assert_equal ~cmp:UPZ.equal
    ~printer:(SrkUtil.mk_show (UPZ.pp Format.pp_print_int))
    seq1
    (UPZ.mul seq1 UPZ.one);
  assert_equal ~cmp:UPZ.equal
    ~printer:(SrkUtil.mk_show (UPZ.pp Format.pp_print_int))
    UPZ.zero
    (UPZ.mul seq1 UPZ.zero);
  assert_equal ~cmp:UPZ.equal
    ~printer:(SrkUtil.mk_show (UPZ.pp Format.pp_print_int))
    (UPZ.make [1] [4; 9; 2; 6; 6; 3])
    (UPZ.mul seq1 seq2)

let suite = "Ring" >::: [
    "ups_eq" >:: test_ups_eq;
    "ups_enum" >:: test_ups_enum;
    "test_ups_add" >:: test_ups_add;
    "test_ups_mul" >:: test_ups_mul;
  ]
