open Syntax

type t = DD.closed DD.t

val dump_hull: bool ref
val dump_hull_prefix : string ref

(** False by default unless otherwise set. *)
val lira_retype_as_real: bool ref

(** Purify formula to have only LRA terms before computing the convex hull.
    This only affects [abstract], because purification does not add models
    to the solver for future exploitation.
    TODO: This should be done by the caller in future.

    The default is true.
 *)
val purify_formula: bool ref

(** (If [lira_retype_as_real] is false)
    Given terms [t_0, ..., t_n], compute the closed convex hull of all points
    [{(t_0(x), ..., t_n(x)) : x |= F}], where [F] is the underlying formula of
    the solver.
    [F] should contain only LRA terms (e.g., no floor, mod, division); if not,
    [purify_formula] should be set.

    If [lira_retype_as_real] is true,
    the convex hull is that of [{(t_0(x), ..., t_n(x)) : x |= F'}],
    where [F'] is the same as [F] except that integer-typed symbols are
    replaced with real-typed ones.
    In this case, the state of the solver is unchanged.
    [F] should contain only LRA terms (e.g., no floor, mod, division); if not,
    [purify_formula] should be set.

    The state of the solver is unchanged if [purify_formula] is true.
*)
val abstract : 'a Abstract.Solver.t ->
               ?man:(DD.closed Apron.Manager.t) ->
               ?bottom:(t option) ->
               'a arith_term array ->
               t

(** Same as [abstract], with [lira_retype_as_real] and [purify_formula] having the
    same effects.
 *)
val conv_hull : ?man:(DD.closed Apron.Manager.t) ->
                'a context ->
                'a formula ->
                ('a arith_term) array ->
                DD.closed DD.t

(** Given a solver containing formula [F],
    terms [t_0, ..., t_n], and a model [m],
    compute a subset of the closed convex hull of
    [{(t_0(x), ..., t_n(x)) : x |= F}] that contains [m].
    [F] should contain only LRA terms (e.g., no floor, mod, division).

    The flags [lira_retype_as_real] and [purify_formula] have no effect here.
 *)
val of_model_lira: 'a Abstract.Solver.t ->
                   (DD.closed Apron.Manager.t) ->
                   ('a arith_term) array ->
                   'a Abstract.smt_model ->
                   DD.closed DD.t

val of_model_lirr : 'a Abstract.Solver.t ->
  (DD.closed Apron.Manager.t) ->
  ('a arith_term) array ->
  'a Abstract.smt_model ->
  DD.closed DD.t
