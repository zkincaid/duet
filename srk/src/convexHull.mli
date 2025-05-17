open Syntax

type t = DD.closed DD.t

(** If [enable_lira] is true, integrality constraints in the formula
    are respected.
    Otherwise, the convex hull is that of the (models of the) real relaxation of
    the formula; integrality constraints, including implicit ones corresponding to
    integer-typed symbols, are dropped.
    The default is [false] to conform to tests.
 *)
val enable_lira: bool ref

val dump_hull: bool ref
val dump_hull_prefix : string ref

(** Given terms [t_0,...,t_n], compute the closed convex hull all points [ {
   (t_0(x),...,t_n(x)) : x |= F } ], where [F] is the underlying formula of
   the solver. *)
val abstract : 'a Abstract.Solver.t ->
               ?man:(DD.closed Apron.Manager.t) ->
               ?bottom:(t option) ->
               'a arith_term array ->
               t

(** Given a formula [F] and terms [t_0,...,t_n], compute the closed convex
   hull all points [ { (t_0(x),...,t_n(x)) : x |= F } ]. *)
val conv_hull : ?man:(DD.closed Apron.Manager.t) ->
                'a context ->
                'a formula ->
                ('a arith_term) array ->
                DD.closed DD.t

val of_model_lira : 'a Abstract.Solver.t ->
  (DD.closed Apron.Manager.t) ->
  ('a arith_term) array ->
  'a Abstract.smt_model ->
  DD.closed DD.t

val of_model_lirr : 'a Abstract.Solver.t ->
  (DD.closed Apron.Manager.t) ->
  ('a arith_term) array ->
  'a Abstract.smt_model ->
  DD.closed DD.t
