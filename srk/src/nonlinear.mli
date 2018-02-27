(** Operations for manipulating non-linear terms and formulas. *)
open Syntax

(** Ensure that a context has the following named symbols
    - [mul] (real multiplication)
    - [imul] (integer multiplication)
    - [mod] (real modulo)
    - [imod] (integer modulo)
    - [inv] (real inverse).
    - [pow] (real exponentiation)
    - [log] (real logarithm)
    If the symbols are not present in the context [ensure_symbols] registers
    them. *)
val ensure_symbols : 'a context -> unit

(** Replace non-linear arithmetic with uninterpreted functions.  The
    uninterpreted function symbols are named symbols: mul, div, and mod.  This
    rewriter is safe to apply top-down or bottom-up. *)
val uninterpret_rewriter : 'a context ->
  ('a,typ_fo) expr ->
  ('a,typ_fo) expr

(** Replace non-linear uninterpreted functions with interpreted ones.  This
    rewriter is safe to apply top-down or bottom-up. *)
val interpret_rewriter : 'a context ->
  ('a,typ_fo) expr ->
  ('a,typ_fo) expr

(** Replace non-linear arithmetic with uninterpreted functions.  The
    uninterpreted function symbols are named symbols: mul, div, and mod. *)
val uninterpret : 'a context -> ('a,'b) expr -> ('a,'b) expr

(** Replace non-linear uninterpreted functions with interpreted ones. *)
val interpret : 'a context -> ('a,'b) expr -> ('a,'b) expr

(** Compute a linear approximation of a non-linear formula. *)
val linearize : 'a context -> 'a formula -> 'a formula

val mk_log : 'a context -> 'a term -> 'a term -> 'a term

val mk_pow : 'a context -> 'a term -> 'a term -> 'a term
