(*pp camlp4find deriving.syntax *)
open Z3

let context = ref None
let opts = ref [ ("SOFT_TIMEOUT", "10000");
	         ("MODEL_COMPLETION", "true") ]

type lbool = Sat | Unsat | Undef
    deriving (Show)

type ast = Z3.ast
type symbol = Z3.symbol
type symbol_refined = Z3.symbol_refined

let cvt_lbool = function
  | L_TRUE -> Sat
  | L_FALSE -> Unsat
  | L_UNDEF -> Undef

let get_context () =
  match !context with
  | Some c -> c
  | None -> begin
    let ctx = Z3.mk_context (!opts) in
    context := Some ctx;
    ctx
  end
let mk_int_sort () = mk_sort (get_context ()) Sort_int
let mk_bool_sort () = mk_sort (get_context ()) Sort_bool
let mk_real_sort () = mk_sort (get_context ()) Sort_real
let mk_solver () = mk_solver (get_context ())

let ast_to_string ast = ast_to_string (get_context()) ast

let mk_const = mk_const (get_context ())
let mk_int_const x = mk_const x (mk_int_sort ())
let mk_real_const x = mk_const x (mk_real_sort ())
let mk_bool_const x = mk_const x (mk_real_sort ())
let mk_string_symbol = mk_string_symbol (get_context ())
let int_var name = mk_const (mk_string_symbol name) (mk_int_sort ())
let bool_var name = mk_const (mk_string_symbol name) (mk_bool_sort ())
let real_var name = mk_const (mk_string_symbol name) (mk_real_sort ())

(* Propositional logic *)
let mk_true () = mk_true (get_context())
let mk_false () = mk_false (get_context())
let mk_distinct xs = mk_distinct (get_context()) xs
let mk_distinct_list xs = Z3.mk_distinct (get_context()) (Array.of_list xs)
let mk_not = mk_not (get_context())
let mk_ite = mk_ite (get_context())
let mk_iff = mk_iff (get_context())
let mk_implies = mk_implies (get_context())
let mk_xor = mk_xor (get_context())
let mk_and = mk_and (get_context ())
let mk_or = mk_or (get_context ())

(* Arithmetic *)
let mk_add = mk_add (get_context ())
let mk_mul = mk_mul (get_context ())
let mk_sub = mk_sub (get_context ())
let mk_unary_minus = mk_unary_minus (get_context ())
let mk_div = mk_div (get_context ())
let mk_mod = mk_mod (get_context ())
let mk_rem = mk_rem (get_context ())
let mk_power = mk_power (get_context ())

let mk_lt = mk_lt (get_context())
let mk_le = mk_le (get_context())
let mk_gt = mk_gt (get_context())
let mk_ge = mk_ge (get_context())
let mk_eq = mk_eq (get_context())
let mk_int2real = mk_int2real (get_context())
let mk_real2int = mk_real2int (get_context())
let mk_is_int = mk_is_int (get_context())


(* Derived operations not defined in the Z3 API *)
let big_conj xs = Z3.mk_and (get_context()) (BatArray.of_enum xs)
let big_disj xs = Z3.mk_or (get_context ()) (BatArray.of_enum xs)
let conj x y = Z3.mk_and (get_context()) [| x ; y |]
let disj x y = Z3.mk_or (get_context()) [| x ; y |]

let sum xs =
  match BatEnum.peek xs with
  | None -> mk_int (get_context()) 0 (mk_int_sort())
  | Some _ -> Z3.mk_add (get_context()) (BatArray.of_enum xs)
let add x y = Z3.mk_add (get_context()) [| x ; y |]
let product xs = Z3.mk_mul (get_context()) (BatArray.of_enum xs)
let mul x y = Z3.mk_mul (get_context()) [| x ; y |]
let sub x y = Z3.mk_sub (get_context()) [| x ; y |]

let const_int k = mk_int (get_context()) k (mk_int_sort())
let const_qq q =
  Z3.mk_numeral (get_context()) (Numeral.QQ.show q) (mk_real_sort())
let const_zz k =
  Z3.mk_numeral (get_context()) (Numeral.ZZ.show k) (mk_int_sort())

let symbol_refine = Z3.symbol_refine (get_context())

class model m =
object(self)
  val ctx = get_context ()
  val m = m
  method eval_int term =
    match model_eval ctx m term true with
    | Some x -> begin match get_numeral_int ctx x with
      | (true, res) -> res
      | (false, _) -> assert false (* this can actually happen *)
    end
    | None -> assert false
  method eval_zz term =
    match model_eval ctx m term true with
    | Some x -> Numeral.ZZ.of_string (get_numeral_string ctx x)
    | None -> assert false
  method eval_qq term =
    match model_eval ctx m term true with
    | Some x -> Numeral.QQ.of_string (get_numeral_string ctx x)
    | None -> assert false
  method to_string () = model_to_string ctx m
end

class solver =
object(self)
  val s = mk_solver ()
  val ctx = get_context ()
  method assrt phi = solver_assert ctx s phi
  method check () = cvt_lbool (solver_check ctx s)
  method check_assumptions assumptions =
    cvt_lbool (solver_check_assumptions ctx s assumptions)
  method get_model () = new model (solver_get_model ctx s)
  method push () = solver_push ctx s
  method pop () = solver_pop ctx s 1
  method reset () = solver_reset ctx s
  method get_num_scopes () = solver_get_num_scopes ctx s
  method get_assertions () = solver_get_assertions ctx s
  method get_proof () = solver_get_proof ctx s
  method get_unsat_core () = solver_get_unsat_core ctx s
  method get_reason_unknown () = solver_get_reason_unknown ctx s
  method get_statistics () = solver_get_statistics ctx s
  method to_string () = solver_to_string ctx s
end

module Syntax = struct
  let ( + ) x y = add x y
  let ( - ) x y = sub x y
  let ( * ) x y = mul x y
  let ( / ) x y = mk_div x y
  let ( && ) x y = conj x y
  let ( || ) x y = disj x y
  let ( == ) x y = mk_eq x y
  let ( < ) x y = mk_lt x y
  let ( > ) x y = mk_gt x y
  let ( <= ) x y = mk_le x y
  let ( >= ) x y = mk_ge x y

  let ( ~$ ) x = int_var x
  let ( ~@ ) x = const_int x
end
