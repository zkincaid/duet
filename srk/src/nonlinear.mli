open Syntax

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

val uninterpret : 'a context -> ('a,'b) expr -> ('a,'b) expr

val interpret : 'a context -> ('a,'b) expr -> ('a,'b) expr

(** Compute a linear approximation of a non-linear formula. *)
val linearize : 'a context -> 'a formula -> 'a formula
