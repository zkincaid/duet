open Syntax
open Smt

val affine_hull : 'a smt_context -> 'a formula -> symbol list -> 'a term list

val boxify : 'a smt_context -> 'a formula -> 'a term list -> 'a formula
