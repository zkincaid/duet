(** (Closed) Convex hulls for LIRA, LIA, and LRA formulas.

    For a formula [F] in a solver or given directly as input, and
    set of linear/affine terms [T]:

    - LIRA abstraction algorithms compute the closed convex hull of the set of
      models of [exists X: real. F /\ /\_{x} Int(x) /\ /\_{t in T} y_t = t],
      where the second conjunct ranges over variables [x] of integer type that
      occur in [F], and each variable [y_t] is fresh.

    - LIA abstraction algorithms compute the closed convex hull of the set of
      models of [exists X: real. F /\ /\_{x} Int(x) /\ /\_{t in T} y_t = t],
      where the second conjunct ranges over all variables [x] that occur in [F],
      each variable [y_t] is fresh,
      and each term [t] has integer coefficients.

      If some variable [x] in [F] is not of integer type, or if some term [t]
      has non-integer coefficients, the result may be unsound
      (i.e., not an over-approximation) in general.

    - LRA abstraction algorithms compute the closed convex hull of the set of
      models of [exists X: real. F /\ /\_{t in T} y_t = t],
      where each [y_t] is fresh, and [F] is a formula that is free of [is_int]
      atoms.

      If some variable [x] in [F] is integer-typed, the result is some set that
      contains [exists X of declared types. F /\ /\_{t in T} y_t = t]
      while contained in [exists X: real. F /\ /\_{t in T} y_t = t].

    [F] must have only LRA terms, and hence be free of floor, mod, non-trivial
    division, etc. This can be done by preprocessing via
    [Syntax.eliminate_floor_mod_div], which introduces fresh integer-valued
    variables.

    For global/classical algorithms (baselines), [F] should also be free of
    [is_int] literals, e.g., removed using
    [Syntax.eliminate_floor_mod_div_int], which introduces fresh integer-valued
    variables.
*)

open Syntax

(** A local abstraction abstracts (maps) a concept and a model satisfying the
  concept to a target concept and an interpretation of the model
  (its "translation") that satisfies the target concept.
*)
type ('concept1, 'model1, 'concept2, 'model2) local_abstraction =
  ('concept1 * 'model1) -> ('concept2 * 'model2)

(** Local abstractions for computing convex hulls *)
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
    -> Symbol.Set.t (* abstract formulas over this set of symbols *)
    -> 'a Syntax.arith_term array (* to linear inequalities in these terms *)
    -> 'a lira_to_polyhedron_abs

  (** Local abstraction for LIRA formulas using only LP-PCone,
    i.e., the interleaving of the subspace/polyhedron-plus-recession-cone
    abstraction and local real projection.
    *)
  val cch_lira_lp_pcone: man:DD.closed Apron.Manager.t
    -> 'a Syntax.context
    -> Symbol.Set.t
    -> 'a Syntax.arith_term array
    -> 'a lira_to_polyhedron_abs

  (** Local abstraction for LIRA formulas using only
    local LIRA projection followed by an under-approximate convex hull of
    integer points within the projection.
    *)
  val cch_lira_lplh: man:DD.closed Apron.Manager.t
    -> ?epsilon: QQ.t
    -> 'a Syntax.context
    -> Symbol.Set.t
    -> 'a Syntax.arith_term array
    -> 'a lira_to_polyhedron_abs

  (** Local abstraction for LRA formulas.
    Input formula must be in core LIRA with LRA terms, and the abstraction
    ignores all [is_int] atoms and ignores integrality of symbols.
    The result is a sound over-approximation if no [is_int] atoms are present.
  *)
  val cch_lra: man:DD.closed Apron.Manager.t
    -> 'a Syntax.context
    -> Symbol.Set.t
    -> 'a Syntax.arith_term array
    -> 'a lira_to_polyhedron_abs

  val cch_lra_hull_then_project: man:DD.closed Apron.Manager.t
    -> 'a context 
    -> Symbol.Set.t -> 'a arith_term array -> 'a lira_to_polyhedron_abs

  (** Local abstraction for LIA formulas.
    Input formula must be in core LIRA with LRA terms, and the abstraction
    assumes that all symbols are integer-typed.
    TODO: Must target terms have integer coefficients?
  *)
  val cch_lia: man:DD.closed Apron.Manager.t
    -> 'a Syntax.context
    -> Symbol.Set.t
    -> 'a Syntax.arith_term array
    -> 'a lira_to_polyhedron_abs

  (** Local abstraction for LIRA formulas by taking the path
    cube implicant
    --> convex hull of points (i.e., a polyhedron)
        satisfying implicant with all [is_int] dropped
    --> apply [hull] to this convex hull
    --> projection of this hull.
    If the formula is an LRA formula with no integer-typed symbols, or if a
    sound over-approximation suffices, [hull] need not be given.
  *)
  (*
  val cch_hull_then_project: DD.closed Apron.Manager.t
    -> ?hull: (DD.closed DD.t -> DD.closed DD.t)
    -> 'a Syntax.context
    -> Symbol.Set.t
    -> 'a Syntax.arith_term array
    -> 'a lira_to_polyhedron_abs
  *)

  val cch_lia_hull_then_project: [`GomoryChvatal | `Normaliz ] ->
    man:DD.closed Apron.Manager.t ->
    'a context ->
    Symbol.Set.t ->
    'a arith_term array ->
    'a lira_to_polyhedron_abs

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
