open Syntax

(** A local abstraction abstracts (maps) a concept and a model satisfying the
    concept to a target concept and an interpretation of the model
    (its "translation") that satisfies the target concept.
*)
type ('concept1, 'model1, 'concept2, 'model2) local_abstraction =
  ('concept1 * 'model1) -> ('concept2 * 'model2)

(** Local abstractions for computing closed convex hulls.

  For a formula [F] in symbols [X] in a solver or given directly as input, and
  set of linear/affine terms [T]:

  - LIRA abstraction algorithms compute the closed convex hull of the set of
    models of [exists X: real. F /\ /\_{x} Int(x) /\ /\_{t in T} y_t = t],
    where the second conjunct ranges over variables [x] of integer type that
    occur in [F], and each variable [y_t] is fresh.

  - LIA abstraction computes the closed convex hull of the set of
    models of [exists X: real. F /\ /\_{x} Int(x) /\ /\_{t in T} y_t = t],
    where the second conjunct ranges over all variables [x] that occur in [F],
    each variable [y_t] is fresh,.

    If some variable [x] in [F] is not of integer type, the result may be
    unsound (i.e., not an over-approximation) in general.

  - LRA abstraction computes the closed convex hull of the set of
    models of [exists X: real. F' /\ /\_{t in T} y_t = t],
    where each [y_t] is fresh, where [F'] is [F] with [is_int] atoms

    [is_int] atoms in [F] are ignored,
    and integrality of symbols is taken into account by the solver.
    The result is then a sound over-approximation of the convex hull of
    integer-real points satisfying [F] if [is_int] only occurs positively in [F].

  [F] must have only LRA terms, and hence be free of floor, mod, non-trivial
  division, etc. This can be done by preprocessing via
  [Syntax.eliminate_floor_mod_div], which introduces fresh integer-valued
  variables.
*)
module ConvexHull : sig

  type 'a lira_to_polyhedron_abs =
    ('a formula, 'a Interpretation.interpretation, DD.closed DD.t, (int -> QQ.t))
    local_abstraction

  (** Local abstraction for core LIRA formulas, i.e., formulas whose terms
      are LRA terms, and whose atoms are inequalities and [is_int].
      [cch man srk symbols terms] is a local abstraction that abstracts any
      core LIRA formula in [symbols] to a conjunction of linear inequalities over
      [terms], i.e., a DD polyhedron, managed by [man].
  *)
  val cch_lira: man:DD.closed Apron.Manager.t
    -> ?epsilon: QQ.t
    -> 'a Syntax.context
    -> 'a Syntax.arith_term array (* to linear inequalities in these terms *)
    -> 'a lira_to_polyhedron_abs

  (** Local abstraction for LRA formulas.
    Input formula must be in core LIRA with LRA terms, and the abstraction
    ignores all [is_int] atoms and ignores integrality of symbols.
    The result is a sound over-approximation if no [is_int] atoms are present.
  *)
  val cch_lra: man:DD.closed Apron.Manager.t
    -> 'a Syntax.context
    -> 'a Syntax.arith_term array
    -> 'a lira_to_polyhedron_abs

  (** Local abstraction for LIA formulas.
    Input formula must be in core LIRA with LRA terms, and the abstraction
    assumes that all symbols are integer-typed.
  *)
  val cch_lia: man:DD.closed Apron.Manager.t
    -> 'a Syntax.context
    -> 'a Syntax.arith_term array
    -> 'a lira_to_polyhedron_abs

end

type plt_constraints
type virtual_term

val select_vt : int -> (int -> QQ.t) -> plt_constraints -> virtual_term
val virtual_subst : 'a Syntax.context ->
                    ?vec_of_sym:(Syntax.symbol -> Linear.QQVector.t) ->
                    ?term_of_dim:('a Syntax.context -> int -> 'a Syntax.arith_term) ->
                    (int * virtual_term) list ->
                    'a Syntax.formula ->
                    'a Syntax.formula

val virtual_subst_plt : (int * virtual_term) list -> plt_constraints -> plt_constraints

val select_plt : 'a Syntax.context ->
                 ?vec_of_sym:(Syntax.symbol -> Linear.QQVector.t) ->
                 'a Syntax.formula ->
                 'a Interpretation.interpretation ->
                 plt_constraints option

val local_project_plt : elim:(int -> bool) ->
                        (int -> QQ.t) ->
                        plt_constraints ->
                        plt_constraints
val poly_part : plt_constraints -> (Polyhedron.constraint_kind * Linear.QQVector.t) list
val lattice_part : plt_constraints -> Linear.QQVector.t list
val tiling_part : plt_constraints -> Linear.QQVector.t list
val make_plt_constraints :
  ?lattice_part:Linear.QQVector.t list ->
  ?tiling_part:Linear.QQVector.t list ->
  (Polyhedron.constraint_kind * Linear.QQVector.t) list ->
  plt_constraints
val formula_of_plt : 'a Syntax.context ->
                     ?term_of_dim:('a Syntax.context -> int -> 'a Syntax.arith_term) ->
                     plt_constraints ->
                     'a Syntax.formula
