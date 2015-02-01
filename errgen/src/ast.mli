open Ark
open ArkPervasives

type aexp_type =
  Real_const of QQ.t
| Sum_exp of (aexp_type * aexp_type)
| Diff_exp of (aexp_type * aexp_type) 
| Mult_exp of (aexp_type * aexp_type) 
| Div_exp of (aexp_type * aexp_type)
| Var_exp of string
| Unneg_exp of aexp_type 
| Havoc_aexp
    deriving (Compare, Show)

type bexp_type = 
 Bool_const of bool 
| Eq_exp of (aexp_type * aexp_type)
| Ne_exp of (aexp_type * aexp_type)
| Gt_exp of (aexp_type * aexp_type)
| Lt_exp of (aexp_type * aexp_type)
| Ge_exp of (aexp_type * aexp_type)
| Le_exp of (aexp_type * aexp_type)
| And_exp of (bexp_type * bexp_type)
| Not_exp of bexp_type
| Or_exp of (bexp_type * bexp_type)
| Havoc_bexp
    deriving (Compare, Show)

type cmd_type =
  Skip
| Assign of (string * aexp_type) 
| Assert of bexp_type
| Print of aexp_type
| Assume of bexp_type
    deriving (Compare, Show)

type stmt_type = 
  Cmd of cmd_type
| Seq of (stmt_type * stmt_type)
| Ite of (bexp_type * stmt_type * stmt_type)
| While of (bexp_type * stmt_type * bool)
    deriving (Show)

type prog_type = 
  Prog of stmt_type 

val aexp_to_string : aexp_type -> string
val bexp_to_string : bexp_type -> string

val collect_vars : stmt_type -> string list

val primify : string -> string
val unprimify : string -> string
val primify_aexp : aexp_type -> aexp_type
val primify_bexp : bexp_type -> bexp_type
val primify_cmd : cmd_type -> cmd_type

val nnf : bexp_type -> bexp_type
val negate : bexp_type -> bexp_type
