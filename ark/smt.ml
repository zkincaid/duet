open Z3
open ArkPervasives

let context = ref None
let opts = ref [ ("timeout", "5000");
	         ("model", "true") ]

type lbool = Sat | Unsat | Undef
    deriving (Show)

type ast = Expr.expr
type symbol = Symbol.symbol
type symbol_refined = Symbol_string of string | Symbol_int of int

let symbol_refine sym =
  if Symbol.is_int_symbol sym then Symbol_int (Symbol.get_int sym)
  else Symbol_string (Symbol.get_string sym)

let cvt_lbool = function
  | Solver.SATISFIABLE -> Sat
  | Solver.UNSATISFIABLE -> Unsat
  | Solver.UNKNOWN -> Undef

let get_context () =
  match !context with
  | Some c -> c
  | None -> begin
    let ctx = Z3.mk_context (!opts) in
    context := Some ctx;
    ctx
  end

let mk_int_sort () = Arithmetic.Integer.mk_sort (get_context ())
let mk_bool_sort () = Boolean.mk_sort (get_context ())
let mk_real_sort () = Arithmetic.Real.mk_sort (get_context ())
let mk_solver () = Solver.mk_solver (get_context ()) None
let mk_fixedpoint () = Fixedpoint.mk_fixedpoint (get_context ())

let ast_to_string ast = Expr.to_string ast

let mk_const = Expr.mk_const (get_context ())
let mk_int_const x = mk_const x (mk_int_sort ())
let mk_real_const x = mk_const x (mk_real_sort ())
let mk_bool_const x = mk_const x (mk_real_sort ())
let mk_string_symbol = Symbol.mk_string (get_context ())
let mk_int_symbol = Symbol.mk_int (get_context ())
let int_var name = mk_const (mk_string_symbol name) (mk_int_sort ())
let bool_var name = mk_const (mk_string_symbol name) (mk_bool_sort ())
let real_var name = mk_const (mk_string_symbol name) (mk_real_sort ())

(* Propositional logic *)
let mk_true () = Boolean.mk_true (get_context())
let mk_false () = Boolean.mk_false (get_context())
let mk_distinct xs = Boolean.mk_distinct (get_context()) xs
let mk_not = Boolean.mk_not (get_context())
let mk_ite = Boolean.mk_ite (get_context())
let mk_iff = Boolean.mk_iff (get_context())
let mk_implies = Boolean.mk_implies (get_context())
let mk_xor = Boolean.mk_xor (get_context())
let mk_and = Boolean.mk_and (get_context ())
let mk_or = Boolean.mk_or (get_context ())

(* Arithmetic *)
let mk_add = Arithmetic.mk_add (get_context ())
let mk_mul = Arithmetic.mk_mul (get_context ())
let mk_sub = Arithmetic.mk_sub (get_context ())
let mk_unary_minus = Arithmetic.mk_unary_minus (get_context ())
let mk_div = Arithmetic.mk_div (get_context ())
let mk_mod = Arithmetic.Integer.mk_mod (get_context ())
let mk_rem = Arithmetic.Integer.mk_rem (get_context ())
let mk_power = Arithmetic.mk_power (get_context ())

let mk_lt = Arithmetic.mk_lt (get_context())
let mk_le = Arithmetic.mk_le (get_context())
let mk_gt = Arithmetic.mk_gt (get_context())
let mk_ge = Arithmetic.mk_ge (get_context())
let mk_eq = Boolean.mk_eq (get_context())
let mk_int2real = Arithmetic.Integer.mk_int2real (get_context())
let mk_real2int = Arithmetic.Real.mk_real2int (get_context())
let mk_is_int = Arithmetic.Real.mk_is_integer (get_context())

let mk_func_decl sym args ret =
  FuncDecl.mk_func_decl (get_context()) sym args ret
let mk_app f args = Expr.mk_app (get_context()) f args
let mk_exists_const vars phi =
  Quantifier.expr_of_quantifier
    (Quantifier.mk_exists_const (get_context()) vars phi None [] [] None None)
let mk_forall_const vars phi =
  Quantifier.expr_of_quantifier
    (Quantifier.mk_forall_const (get_context()) vars phi None [] [] None None)

(* Derived operations not defined in the Z3 API *)
let big_conj xs = Boolean.mk_and (get_context()) (BatList.of_enum xs)
let big_disj xs = Boolean.mk_or (get_context ()) (BatList.of_enum xs)
let conj x y = Boolean.mk_and (get_context()) [x ; y]
let disj x y = Boolean.mk_or (get_context()) [x ; y]

let sum xs =
  match BatEnum.peek xs with
  | None -> Arithmetic.Integer.mk_numeral_i (get_context()) 0
  | Some _ -> Arithmetic.mk_add (get_context()) (BatList.of_enum xs)
let add x y = Arithmetic.mk_add (get_context()) [x ; y]
let product xs = Arithmetic.mk_mul (get_context()) (BatList.of_enum xs)
let mul x y = Arithmetic.mk_mul (get_context()) [x ; y]
let sub x y = Arithmetic.mk_sub (get_context()) [x ; y]

let const_int k = Arithmetic.Integer.mk_numeral_i (get_context()) k
let const_qq q =
  Arithmetic.Real.mk_numeral_s (get_context()) (QQ.show q)
let const_zz k =
  Arithmetic.Integer.mk_numeral_s (get_context()) (ZZ.show k)

class model m =
object(self)
  val ctx = get_context ()
  val m = m
  method eval_int term =
    match Model.eval m term true with
    | Some x -> Arithmetic.Integer.get_int x (* todo: overflow *)
    | None -> assert false
  method eval_zz term =
    match Model.eval m term true with
    | Some x -> ZZ.of_string (Arithmetic.Integer.numeral_to_string x)
    | None -> assert false
  method eval_qq term =
    match Model.eval m term true with
    | Some x -> QQ.of_string (Arithmetic.Real.numeral_to_string x)
    | None -> assert false
  method sat phi =
    match Model.eval m phi true with
    | Some x -> begin match Boolean.get_bool_value x with
      | Z3enums.L_TRUE -> true
      | Z3enums.L_FALSE -> false
      | Z3enums.L_UNDEF -> assert false
    end
    | None -> assert false

  method to_string () = Model.to_string m
end

class solver =
object(self)
  val s = mk_solver ()
  val ctx = get_context ()
  method assrt phi = Solver.add s [phi]
  method check () = cvt_lbool (Solver.check s [])
  method check_assumptions assumptions =
    cvt_lbool (Solver.check s assumptions)
  method get_model () = match Solver.get_model s with
  | Some m -> new model m
  | None -> failwith "solver.get_model: No model"
  method push () = Solver.push s
  method pop () = Solver.pop s 1
  method reset () = Solver.reset s
  method get_num_scopes () = Solver.get_num_scopes s
  method get_assertions () = Solver.get_assertions s
  method get_proof () = Solver.get_proof s
  method get_unsat_core () = Solver.get_unsat_core s
  method get_reason_unknown () = Solver.get_reason_unknown s
  method get_statistics () = Solver.get_statistics s
  method to_string () = Solver.to_string s
end

class fixedpoint =
object(self)
  val fp = mk_fixedpoint ()
  val ctx = get_context ()
  method assrt phi = Fixedpoint.add fp [phi]
  method add_rule ast symbol = Fixedpoint.add_rule fp ast symbol
  method query ast = Fixedpoint.query fp ast
  method query_relations rels = Fixedpoint.query_r fp rels
  method get_answer () = Fixedpoint.get_answer fp
  method get_reason_unknown () = Fixedpoint.get_reason_unknown fp
  method register_relation pred = Fixedpoint.register_relation fp pred
  method set_predicate_representation fp pred rep =
    Fixedpoint.set_predicate_representation fp pred rep
  method to_string () = Fixedpoint.to_string fp
  method push () = Fixedpoint.push fp
  method pop () = Fixedpoint.pop fp
  method get_num_levels pred = Fixedpoint.get_num_levels fp pred
  method get_cover_delta n pred = Fixedpoint.get_cover_delta fp n pred
  method set_params params = Fixedpoint.set_params fp params
  method get_help () = Fixedpoint.get_help fp
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
