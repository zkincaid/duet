open Syntax
open BatPervasives

let min_coeff = ref (-10)
let max_coeff = ref 10
let quantifier_prefix =
  ref [ `Forall; `Forall; `Forall; `Forall;
        `Exists; `Exists; `Exists; `Exists;
        `Forall; `Forall; `Forall; `Forall ]

let formula_uq_proba = ref 0.9
let formula_uq_depth = ref 5
let number_of_monomials_per_expression = ref 5
let dense = ref false

let mk_random_coeff srk =
  mk_real srk
    (QQ.of_int ((Random.int (!max_coeff - !min_coeff + 1)) + !min_coeff))

let mk_random_variable srk =
  mk_var srk (Random.int (List.length (!quantifier_prefix))) `TyInt

let mk_random_term srk =
  if !dense then
    (0 -- ((List.length (!quantifier_prefix)) - 1))
    /@ (fun i -> mk_mul srk [mk_random_coeff srk; mk_var srk i `TyInt])
    |> BatList.of_enum
    |> mk_add srk
  else
    (1 -- (1 + (Random.int (!number_of_monomials_per_expression) - 1)))
    /@ (fun _ -> mk_mul srk [mk_random_coeff srk; mk_random_variable srk])
    |> BatList.of_enum
    |> mk_add srk

let rec mk_random_qf_formula srk depth =
  if depth <= 0 || Random.float 1.0 >= !formula_uq_proba then
    mk_leq srk (mk_random_term srk) (mk_random_coeff srk)
  else
    let psis =
      [ mk_random_qf_formula srk (depth-1);
        mk_random_qf_formula srk (depth-1) ]
    in
    if Random.bool ()
    then mk_and srk psis
    else mk_or srk psis

let mk_random_formula srk =
  let n = ref 0 in
  let mk_name () =
    incr n;
    "v" ^ (string_of_int (!n))
  in
  List.fold_right
    (fun qt phi ->
       match qt with
       | `Exists -> mk_exists srk ~name:(mk_name()) `TyInt phi
       | `Forall -> mk_forall srk ~name:(mk_name()) `TyInt phi)
    (!quantifier_prefix)
    (mk_random_qf_formula srk (!formula_uq_depth))
