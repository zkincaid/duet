open Srk
open OUnit

module UP = Sequence.UltimatelyPeriodic
module P = Sequence.Periodic

(* Ultimately periodic sequences of integers *)
module UPZ = struct
  type t = int UP.t
  let add = UP.map2 ( + )
  let mul = UP.map2 ( * )
  let negate = UP.map (fun x -> -x)
  let zero = UP.make [] [0]
  let one = UP.make [] [1]
end

let assert_equal_upz x y =
  assert_equal ~cmp:UP.equal ~printer:(SrkUtil.mk_show (UP.pp Format.pp_print_int)) x y

let assert_equal_pz x y =
  assert_equal ~cmp:P.equal ~printer:(SrkUtil.mk_show (P.pp Format.pp_print_int)) x y

let exp_mod_seq base modulus =
  let f x = (x * base) mod modulus in
  UP.unfold f 1


let suite = "Sequence" >::: [
      "ups_eq" >:: (fun () ->
        let seq1 =
          UP.make [] [1; 2; 3]
        in
        let seq2 =
          UP.make [1] [2; 3; 1]
        in
        let seq3 =
          UP.make [] [1; 2; 3; 1; 2; 3]
        in
        assert_equal_upz seq1 seq2;
        assert_equal_upz seq1 seq3;
        assert_equal_upz seq3 seq2);

      "ups_enum" >:: (fun () ->
        let seq = UP.make [1; 2] [3; 4; 5] in
        assert_equal
          [1;2;3;4;5;3;4;5;3;4]
          (BatList.of_enum (BatEnum.take 10 (UP.enum seq))));
          
      "ups_add" >:: (fun () ->
        let seq1 = UP.make [1; 2] [3; 4] in
        let seq2 = UP.make [1] [2; 3; 4] in
        assert_equal_upz seq1 (UPZ.add seq1 UPZ.zero);
        assert_equal_upz
          (UP.make [2; 4] [6; 8; 5; 7; 7; 6])
          (UPZ.add seq1 seq2);
        assert_equal_upz
          UPZ.zero
          (UPZ.add
             (UPZ.add seq1 seq2)
             (UPZ.add (UPZ.negate seq2) (UPZ.negate seq1))));
      
      "ups_mul" >:: (fun () ->
        let seq1 = UP.make [1] [2; 3] in
        let seq2 = UP.make [] [1; 2; 3] in
        assert_equal_upz seq1 (UPZ.mul seq1 UPZ.one);
        assert_equal_upz UPZ.zero (UPZ.mul seq1 UPZ.zero);
        assert_equal_upz
          (UP.make [1] [4; 9; 2; 6; 6; 3])
          (UPZ.mul seq1 seq2));

      "unfold1" >:: (fun () ->
        let seq = exp_mod_seq 2 32 in
        assert_equal_upz seq (UP.make [1; 2; 4; 8; 16] [0]));

      "unfold2" >:: (fun () ->
        let seq = exp_mod_seq 2 6 in
        assert_equal_upz seq (UP.make [1] [2; 4]));

      "unfold3" >:: (fun () ->
        let seq = exp_mod_seq 3 5 in
        assert_equal_upz seq (UP.make [] [1; 3; 4; 2]));

      "unfold4" >:: (fun () ->
        assert_equal_upz (UP.unfold (fun _ -> 0) 0) (UP.make [] [0]);
        assert_equal_upz (UP.unfold (fun _ -> 1) 0) (UP.make [0] [1]));

      "periodic_approx" >:: (fun () ->
        let make_approx t p = Sequence.periodic_approx (UP.make t p) in
        assert_equal_pz (make_approx [] [1; 2; 3]) (P.make [1; 2; 3]);
        assert_equal_pz (make_approx [0] [1; 2; 3]) (P.make [3; 1; 2]);
        assert_equal_pz (make_approx [1; 2] [3; 4]) (P.make [3; 4]))
    ]
