open Ark
open ArkPervasives

type aexp_type =
  Real_const of QQ.t
| Sum_exp of (aexp_type * aexp_type)
| Diff_exp of (aexp_type * aexp_type) 
| Mult_exp of (aexp_type * aexp_type) 
| Var_exp of string
| Unneg_exp of aexp_type 
| Havoc_aexp

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

type stmt_type =  
   Skip 
|  Assign of (string * aexp_type) 
| Seq of (stmt_type * stmt_type)
| Ite of (bexp_type * stmt_type * stmt_type)
| While of (bexp_type * stmt_type)
| Assert of bexp_type
| Print of aexp_type
| Assume of bexp_type    

type prog_type = 
  Prog of stmt_type 
