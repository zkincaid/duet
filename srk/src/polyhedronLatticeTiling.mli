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

type lira_abstraction =
  | PolyReccone
    (** Local projection of the subpolyhedron contained in the
        integer class of model (roughly) + (i.e., Minkowski sum)
        recession cone of the local projection of the
        Loos-Weispfenning MBP subpolyhedron.
     *)
  | LiraLPLH of QQ.t option
    (** Local projection of the PLT followed by taking local hull (via HKMMZ) *)
  | PolyReccone_LPLH of QQ.t option
    (** The same as PolyReccone, but joined with the local hull
        (LH; via HKMMZ) of the local projection (LP) of the PLT.
        Strict inequalities are rounded to loose ones by shifting
        using the option; if unspecified, some internal choice is made.
     *)

(** LIA abstraction requires that every variable is integer-valued
    and that the target terms have integer coefficients.
 *)
type lia_abstraction =
  | HullThenProject of [`GomoryChvatal | `Normaliz]
  (** Baseline. Formula should not have [is_int] literals. *)
  | LiaLPLH
  (** Local projection of PLT followed by taking local hull. *)

(** LRA abstraction ignores all [is_int] constraints in the implicant and
    integrality of variables.
    (But the solver finds models that respect integrality of variables.
    An LRA over-approximation should in principle be the LRA abstraction of
    the real relaxation of the formula, where we replace all integer-typed
    variables with real-typed ones, via [Syntax.retype].)
 *)
type lra_abstraction =
  | FullProject
  (** Baseline  *)
  | LwMbp
  (** Local projection of Loos-Weispfenning MBP subpolyhedron *)

type abstraction_algorithm =
  | LiraCCH of lira_abstraction
  | LiaCCH of lia_abstraction
  | LraCCH of lra_abstraction

(** [convex_hull_from_lira_model how ~man solver terms model] is a subpolyhedron
    of conv.hull({(terms[0](m), ..., terms[len(terms)](m): m |= F)}) that
    contains [model], where [F] is the formula in [solver].
    This polyhedron is computed using [how].
 *)
val convex_hull_from_lira_model:
  abstraction_algorithm ->
  ?man:(DD.closed Apron.Manager.t) ->
  'a Abstract.Solver.t ->
  ('a Syntax.arith_term) array -> 'a Abstract.smt_model ->
  DD.closed DD.t

(** [abstract how ~man ~bottom solver terms]
    = conv.hull({(terms[0](m), ..., terms[len(terms)](m): m |= F)}),
    where [F] is the formula in [solver].
    This is computed using [how].
    [bottom] has to define a subset of the convex hull.
 *)
val abstract: abstraction_algorithm ->
              ?man:(DD.closed Apron.Manager.t) ->
              ?bottom:(DD.closed DD.t option) ->
              'a Abstract.Solver.t ->
              'a Syntax.arith_term array ->
              DD.closed DD.t

(** [convex_hull how ~man srk F terms]
    = conv.hull({(terms[0](m), ..., terms[len(terms)](m): m |= F)}).
    This is computed using [how].
 *)
val convex_hull: abstraction_algorithm ->
                 ?man:(DD.closed Apron.Manager.t) ->
                 'a Syntax.context -> 'a Syntax.formula ->
                 ('a Syntax.arith_term) Array.t -> DD.closed DD.t
