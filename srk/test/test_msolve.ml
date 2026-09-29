open Srk
open OUnit
open Polynomial

(* Solve polynomials with msolve and check the resulting parametrization: the
   coordinates of the variables, as elements of Q[t]/(m), must be reduced and
   satisfy every polynomial, and m must have one root per solution. *)
let check_parametrization ~solutions variables polynomials =
  skip_if (not (Msolve.available ())) "msolve executable not found";
  let m, coordinates = Msolve.parametrization variables polynomials in
  assert_equal ~printer:string_of_int solutions (QQX.order m);
  assert_equal
    ~printer:string_of_int
    (List.length variables)
    (List.length coordinates);
  List.iter
    (fun coordinate ->
       assert_bool "Coordinate is reduced modulo m"
         (QQX.order coordinate < QQX.order m))
    coordinates;
  let modulo p = snd (QQX.qr p m) in
  let values = List.combine variables coordinates in
  let eval polynomial =
    QQXs.fold
      (fun monomial coefficient sum ->
         let term =
           BatEnum.fold
             (fun term (variable, exponent) ->
                modulo (QQX.mul term (QQX.exp (List.assoc variable values) exponent)))
             (QQX.scalar coefficient)
             (Monomial.enum monomial)
         in
         QQX.add sum term)
      polynomial
      QQX.zero
    |> modulo
  in
  List.iter
    (fun polynomial ->
       assert_bool "Parametrization satisfies the system"
         (QQX.is_zero (eval polynomial)))
    polynomials

let x = QQXs.of_dim
let int k = QQXs.scalar (QQ.of_int k)

(* msolve omits the coordinate of its last variable, which is reconstructed
   from the linear form. *)
let test_one_variable () =
  check_parametrization ~solutions:2 [0] [QQXs.sub (QQXs.exp (x 0) 2) (int 2)]

let test_omitted_last () =
  check_parametrization ~solutions:2 [0; 1]
    [ QQXs.sub (QQXs.exp (x 0) 2) (int 2)
    ; QQXs.sub (x 1) (x 0) ]

(* No variable separates the solutions, so msolve introduces a new variable
   for the linear form; its coordinate must be ignored. *)
let test_introduced_variable () =
  check_parametrization ~solutions:4 [0; 1]
    [ QQXs.sub (QQXs.exp (x 0) 2) (int 2)
    ; QQXs.sub (QQXs.exp (x 1) 2) (int 3) ]

(* Coordinates are returned in the order of the requested variables, which
   need not be contiguous or increasing. *)
let test_variable_order () =
  check_parametrization ~solutions:2 [5; 3]
    [ QQXs.sub (QQXs.exp (x 3) 2) (int 2)
    ; QQXs.sub (x 5) (QQXs.add (x 3) (int 1)) ]

let suite = "Msolve" >::: [
    "one_variable" >:: test_one_variable;
    "omitted_last" >:: test_omitted_last;
    "introduced_variable" >:: test_introduced_variable;
    "variable_order" >:: test_variable_order;
  ]
