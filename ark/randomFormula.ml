open Syntax
open BatPervasives

let min_coeff = ref (-5)
let max_coeff = ref 5
let quantifier_prefix =
  ref [ `Forall; `Forall; `Forall; `Forall;
        `Exists; `Exists; `Exists; `Exists;
        `Forall; `Forall; `Forall; `Forall ]

let formula_uq_proba = ref 0.9
let formula_uq_depth = ref 5
let number_of_monomials_per_expression = ref 5
let dense = ref false

let mk_random_coeff ctx =
  mk_real ctx
    (QQ.of_int ((Random.int (!max_coeff - !min_coeff + 1)) + !min_coeff))

let mk_random_variable ctx =
  mk_var ctx (Random.int (List.length (!quantifier_prefix))) `TyInt

let mk_random_variable ctx =
  let rec go min max =
    if min = max then max
    else if Random.float 1.0 >= 0.6 then
      go min ((min + max) / 2)
    else
      go ((max + min + 1) / 2) max
  in
  mk_var ctx (go 0 (List.length (!quantifier_prefix) - 1)) `TyInt

let mk_random_term ctx =
  if !dense then
    (0 -- ((List.length (!quantifier_prefix)) - 1))
    /@ (fun i -> mk_mul ctx [mk_random_coeff ctx; mk_var ctx i `TyInt])
    |> BatList.of_enum
    |> mk_add ctx
  else
    (1 -- (!number_of_monomials_per_expression))
    /@ (fun _ -> mk_mul ctx [mk_random_coeff ctx; mk_random_variable ctx])
    |> BatList.of_enum
    |> mk_add ctx

let rec mk_random_qf_formula ctx depth =
  if depth <= 0 || Random.float 1.0 >= !formula_uq_proba then
    mk_leq ctx (mk_random_term ctx) (mk_random_coeff ctx)
  else
    let psis =
      [ mk_random_qf_formula ctx (depth-1);
        mk_random_qf_formula ctx (depth-1) ]
    in
    if Random.bool ()
    then mk_and ctx psis
    else mk_or ctx psis

let mk_random_formula ctx =
  let n = ref 0 in
  let mk_name () =
    incr n;
    "v" ^ (string_of_int (!n))
  in
  List.fold_right
    (fun qt phi ->
       match qt with
       | `Exists -> mk_exists ctx ~name:(mk_name()) `TyInt phi
       | `Forall -> mk_forall ctx ~name:(mk_name()) `TyInt phi)
    (!quantifier_prefix)
    (mk_random_qf_formula ctx (!formula_uq_depth))
