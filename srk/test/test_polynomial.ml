open Srk
open OUnit
open Polynomial
open BatPervasives
module RW = Polynomial.RewriteWitness

let mk_qqx vec =
  List.fold_left
    (fun vec (i, k) -> QQX.add_term k i vec)
    QQX.zero
    (List.mapi (fun i k -> (i, QQ.of_int k)) vec)

module QQXsInfix = struct
  let ( + ) = QQXs.add
  let ( - ) = QQXs.sub
  let ( * ) = QQXs.mul
  let int k = QQXs.scalar (QQ.of_int k)
  let dim k = QQXs.of_dim (Char.code k)
end

let assert_equal_qqx p q =
  assert_equal ~cmp:QQX.equal ~printer:QQX.show p q

let assert_equal_qqxs p q =
  let pp_dim formatter i =
    Format.pp_print_string formatter (Char.escaped (Char.chr i))
  in
  let show = SrkUtil.mk_show (QQXs.pp pp_dim) in
  assert_equal ~printer:show ~cmp:QQXs.equal p q

let assert_equal_ideal p q =
  let pp_dim formatter i =
    Format.pp_print_string formatter (Char.escaped (Char.chr i))
  in
  let show = SrkUtil.mk_show (Ideal.pp pp_dim) in
  assert_equal ~printer:show ~cmp:Ideal.equal p q

let test_mul () =
  let p = mk_qqx [1; 1] in
  let q = mk_qqx [-1; 1] in
  let r = mk_qqx [-1; 0; 1] in
  assert_equal_qqx r (QQX.mul p q)

let test_compose1 () = 
  let p = mk_qqx [-1; 1] in
  let q = mk_qqx [-1; 0; 1] in
  let r = mk_qqx [0; -2; 1] in
  assert_equal_qqx r (QQX.compose q p)

let test_compose2 () =
  let p = mk_qqx [1; 0; 1] in
  let q = mk_qqx [1; 2; 3; 4] in
  let r = mk_qqx [10; 0; 20; 0; 15; 0; 4] in
  (*  let r = mk_qqx [6; 0; 8; 0; 3; 0; 0] in*)
  assert_equal_qqx r (QQX.compose q p)

let test_eval () =
  let p = mk_qqx [-1; 2; -3; 4] in
  assert_equal ~printer:QQ.show (QQ.of_int 23) (QQX.eval p (QQ.of_int 2))

let test_summation1 () =
  let p = mk_qqx [2] in
  let r = mk_qqx [2; 2] in
  assert_equal_qqx r (QQX.summation p)

let test_summation2 () = (* Gauss sum *)
  let p = mk_qqx [0; 1] in
  let r =
    QQX.scalar_mul (QQ.inverse (QQ.of_int 2))
      (QQX.mul (mk_qqx [0;1]) (mk_qqx [1;1]))
  in
  assert_equal_qqx r (QQX.summation p)

let test_rewrite1 () =
  let open QQXsInfix in
  let x = dim 'x' in
  let y = dim 'y' in
  let rewrite =
    Rewrite.mk_rewrite Monomial.deglex [
      y * y - (int 2);
      x * x + y * x + (int 1)
    ]
  in
  assert_equal_qqxs (int (-1)) (Rewrite.reduce rewrite (x * x * x * x))

(* Linear system of equations *)
let test_rewrite2 () =
  let open QQXsInfix in
  let x = dim 'x' in
  let y = dim 'y' in
  let z = dim 'z' in
  let rewrite =
    Rewrite.mk_rewrite Monomial.lex [
      (int 2) * x - (int 2) * y + (int 4) * z + (int 2);
      (int 3) * x + (int 2) * y - z - (int 1);
      (int (-2)) * x + y - (int 2) * z;
    ] |> Rewrite.reduce_rewrite
  in
  assert_equal_qqxs (int 1) (Rewrite.reduce rewrite x);
  assert_equal_qqxs (int (-2)) (Rewrite.reduce rewrite y);
  assert_equal_qqxs (int (-2)) (Rewrite.reduce rewrite z)

let test_grobner1 () =
  let open QQXsInfix in
  let a = dim 'a' in
  let b = dim 'b' in
  let c = dim 'c' in
  let x = dim 'x' in
  let y = dim 'y' in
  let z = dim 'z' in
  let rewrite =
    Rewrite.mk_rewrite Monomial.degrevlex [
      a * x * x + b * x + c;
      a * y * y + b * y + c;
      z * (x - y) - (int 1);
    ] |> Rewrite.grobner_basis
  in
  let p = a * x * y - c in
  let q = a * (x + y) + b in
  assert_equal_qqxs (int 0) (Rewrite.reduce rewrite p);
  assert_equal_qqxs (int 0) (Rewrite.reduce rewrite q)

let test_grobner2 () =
  let open QQXsInfix in
  let x = dim 'x' in
  let y = dim 'y' in
  let rewrite =
    Rewrite.mk_rewrite Monomial.degrevlex [
      x * x - y;
      x * x * x - x
    ] |> Rewrite.grobner_basis
  in
  let p = x * y - x in
  let q = y * y - y in
  assert_equal_qqxs (int 0) (Rewrite.reduce rewrite p);
  assert_equal_qqxs (int 0) (Rewrite.reduce rewrite q)

let test_grobner_elim () =
  let open QQXsInfix in
  let x = dim 'x' in
  let y = dim 'y' in
  let elim_order =
    Monomial.block [fun d -> d = (Char.code 'x')] Monomial.degrevlex
  in
  let rewrite =
    Rewrite.mk_rewrite elim_order [
      x - y * y;
      x * x - x
    ] |> Rewrite.grobner_basis
  in
  let p = x * x * y - x in
  let q = y * y * y - y * y in
  assert_equal_qqxs q (Rewrite.reduce rewrite p)

let rec mul_factors = function
  | [] -> QQX.of_term QQ.one 0
  | (p,n)::factors ->
    QQX.mul (QQX.exp p n) (mul_factors factors)

let qqx_of_list = QQX.of_enum % BatList.enum
let qq = QQ.of_int

let factor () =
  let correct_factorization p =
    let (content, factors) = QQX.factor p in
    assert_equal_qqx p (QQX.scalar_mul content (mul_factors factors))
  in
  correct_factorization (qqx_of_list [(qq (-1), 0); (qq 1, 2)]);
  correct_factorization (qqx_of_list [(QQ.of_frac 1 2, 4);
                                      (QQ.of_frac 1 4, 2)])

let intersect_ideal1 () =
  let open QQXsInfix in
  let x = dim 'x' in
  let y = dim 'y' in
  let z = dim 'z' in
  let t = dim 't' in
  let i = Ideal.make [x; y] in
  let j = Ideal.make [z; x - t] in
  let r = Ideal.make [x*z; y*z; x*y - t*y; x*x - t*x] in
  assert_equal_ideal r (Ideal.intersect i j)

let intersect_ideal2 () =
  let open QQXsInfix in
  let w = dim 'w' in
  let x = dim 'x' in
  let y = dim 'y' in
  let z = dim 'z' in
  let i = Ideal.make [z; w] in
  let j = Ideal.make [x + z; y + w] in
  let r = Ideal.product i j in
  assert_equal_ideal r (Ideal.intersect i j)

let intersect_ideal3 () =
  let open QQXsInfix in
  let w = dim 'w' in
  let x = dim 'x' in
  let z = dim 'z' in
  let i = Ideal.make [z; w] in
  let j = Ideal.make [x + z; w] in
  let r = Ideal.make [w; x*z + z*z] in
  assert_equal_ideal r (Ideal.intersect i j)

let product_ideal () =
  let open QQXsInfix in
  let w = dim 'w' in
  let x = dim 'x' in
  let z = dim 'z' in
  let i = Ideal.make [z; w] in
  let j = Ideal.make [x + z; w] in
  let r = Ideal.make [x*z + z*z; z*w; x*w; w*w] in
  assert_equal_ideal r (Ideal.product i j)

let mk_rewrite_witness xs =
  BatList.mapi
    (fun i p -> (p, Witness.of_term (QQXs.negate QQXs.one) i))
    xs
  |> RW.mk_rewrite Monomial.degrevlex
  |> RW.grobner_basis

let qqxs_of_witness generators w =
  BatEnum.fold (fun p (q, i) ->
      QQXs.add p (QQXs.mul q (List.nth generators i)))
    QQXs.zero
    (Polynomial.Witness.enum w)

let assert_rewrite_spec generators rewrite p =
  let (p', w) = RW.reduce rewrite p in
  assert_equal_qqxs p (QQXs.add p' (qqxs_of_witness generators w))

let suite = "Polynomial" >::: [
    "mul" >:: test_mul;
    "compose1" >:: test_compose1;
    "compose2" >:: test_compose2;
    "eval" >:: test_eval;
    "test_summation1" >:: test_summation1;
    "test_summation2" >:: test_summation2;
    "test_rewrite1" >:: test_rewrite1;
    "test_rewrite2" >:: test_rewrite2;
    "test_grobner1" >:: test_grobner1;
    "test_grobner2" >:: test_grobner2;
    "test_grobner_elim" >:: test_grobner_elim;
    "factor" >:: factor;
    "intersect_ideal1" >:: intersect_ideal1;
    "intersect_ideal2" >:: intersect_ideal2;
    "intersect_ideal3" >:: intersect_ideal3;
    "product_ideal" >:: product_ideal

    ; "rewrite_linear" >:: (fun () ->
        let open QQXsInfix in
        let x = dim 'x' in
        let y = dim 'y' in
        let z = dim 'z' in
        let p = (int 2) * x + (int 2) in
        let q = y + z in
        let generators = [p; q] in
        let rewrite = mk_rewrite_witness generators in
        (match RW.zero_witness rewrite p with
         | Some w -> assert_equal_qqxs p (qqxs_of_witness generators w);
         | None -> assert false);
        (match RW.zero_witness rewrite q with
         | Some w -> assert_equal_qqxs q (qqxs_of_witness generators w);
         | None -> assert false);
        assert_rewrite_spec generators rewrite (x + (int 3) * z))

    ; "rewrite_nonlin" >:: (fun () ->
        let open QQXsInfix in
        let x = dim 'x' in
        let y = dim 'y' in
        let z = dim 'z' in
        let p = x - (int 1) in
        let q = y * y - z + x + (int 1) in
        let generators = [p; q] in
        let rewrite = mk_rewrite_witness generators in
        assert_rewrite_spec generators rewrite (x * x);
        assert_rewrite_spec generators rewrite (x * x * y * y + x + y * y))

    ; "rewrite_inconsistent" >:: (fun () ->
        let open QQXsInfix in
        let x = dim 'x' in
        let y = dim 'y' in
        let p = x * x - (int 7) in
        let q = x - y in
        let r = y * y - (int 30) in
        let generators = [p; q; r] in
        let rewrite = mk_rewrite_witness generators in
        assert_rewrite_spec generators rewrite QQXs.one;
        assert_rewrite_spec generators rewrite (p * q * r))

    ; "rewrite_linear_inconsistent" >:: (fun () ->
        let open QQXsInfix in
        let x = dim 'x' in
        let y = dim 'y' in
        let p = (int 2) * x + (int 2) in
        let q = x + y in
        let r = y + (int 3) in
        let generators = [p; q; r] in
        let rewrite = mk_rewrite_witness generators in
        assert_rewrite_spec generators rewrite QQXs.one;
        assert_rewrite_spec generators rewrite (p * x))


    ; "rewrite_gb" >:: (fun () ->
        let open QQXsInfix in
        let x = dim 'x' in
        let y = dim 'y' in
        let z = dim 'z' in
        let p = x * y - (int 1) in
        let q = y * y - z + (int 1) in
        let r = x * z - (y * z) in
        let generators = [p; q; r] in
        let rewrite = mk_rewrite_witness generators in
        assert_rewrite_spec generators rewrite (x * x * y);
        assert_rewrite_spec generators rewrite (x * y * z + y * z + x * z))
  ]
