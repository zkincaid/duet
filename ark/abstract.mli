open Syntax
open Smt

val affine_hull : 'a context -> 'a formula -> symbol list -> 'a term list

val boxify : 'a context -> 'a formula -> 'a term list -> 'a formula

