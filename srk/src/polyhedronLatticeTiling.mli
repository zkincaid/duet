(** Concept space of polyhedron-lattice-tilings (PLTs) *)

module P = Polyhedron
module V = Linear.QQVector

type standard
type intfrac
type 'layout plt

val formula_of_dd:
  'a Syntax.context -> (int -> 'a Syntax.arith_term) -> DD.closed DD.t ->
  'a Syntax.formula

val formula_of_plt:
  'a Syntax.context -> (int -> 'a Syntax.arith_term) -> 'layout plt ->
  'a Syntax.formula

(*
val cooper_project: 'a Syntax.context -> 'a Syntax.formula ->
                    ('a Syntax.arith_term ) Array.t -> standard plt list

val disjunctive_normal_form:
  'a Syntax.context -> base_dim:int -> 'a Syntax.formula ->
  (standard plt list * 'a Syntax.arith_term SrkUtil.Int.Map.t)
 *)

val eager_hermite: bool ref

type abstraction_algorithm =
  | SubspaceCone of [`Standard | `WithHKMMZCone]
  | IntFrac of [`Standard]
  (** IntFrac: Each implicant is first transformed into a formula over a vocabulary of
      fresh variables {x_int, x_frac: x is a variable}, where each [x_int] is
      integer-valued and 0 <= [x_frac] < 1 for each fractional variable.
      This formula is equivalent to the implicant under a standard interpretation
      [x = x_int + x_frac].
      Formulas in this fragment admit quantifier elimination, so this formula
      is locally projected onto variables (corresponding to the terms) to keep.
      Then the mixed integer-hull (with respect to the integer-valued variables)
      is locally computed, i.e., we get a subpolyhedron of the hull,
      and this is mapped to the original space via the linear map defined by
      [x = x_int + x_frac].
   *)
  | LwCooperHKMMZCone
  | ProjectImplicant of
      [ `AssumeReal of [`FullProject | `Lw]
      (** Correct when the formula [F] has no [Int] literals AND all variables
          are of real type.
          [`FullProject] corresponds to the convex hull algorithm in FMCAD'15;
          [`Lw] takes the convex hull of disjuncts computed by
          model-based projection for LRA.
       *)
      | `AssumeInt of
          [ `HullThenProject of [`GomoryChvatal | `Normaliz]
          | `ProjectThenHull of [`GomoryChvatal | `Normaliz]
          ]
        (** Correct when the formula [F] is equivalent modulo the theory of RR to
            [F' /\ /\_{x in variables(F)} Int(x)], where [F'] is the formula
            obtained from [F] by deleting all [Int] literals.
            All variables [v] in [F] that are of integer type should be
            explicitly constrained as integer-valued via [Int(v)].

            [`GomoryChvatal] and [`Normaliz] compute the integer hull using
            respective algorithms.

            [`HullThenProject] takes the integer hull followed by full projection.
            [`ProjectThenHull] does model-based projection using Cooper's algorithm
            and then takes the integer hull.
         *)
      ]

(** [convex_hull_of_lira_model how ~man solver terms model] is a subpolyhedron
    of conv.hull({(terms[0](m), ..., terms[len(terms)](m): m |= F)}) that
    contains [model], where [F] is the formula in [solver].
    This polyhedron is computed using [how].
    All variables [v] in [F] that are of integer type must be explicitly
    constrained in [F] to take on integer values only via [Int(v)].
 *)
val convex_hull_of_lira_model:
  abstraction_algorithm ->
  ?man:(DD.closed Apron.Manager.t) ->
  'a Abstract.Solver.t ->
  ('a Syntax.arith_term) array -> 'a Abstract.smt_model ->
  DD.closed DD.t

(** [abstract how ~man ~bottom solver terms]
    = conv.hull({(terms[0](m), ..., terms[len(terms)](m): m |= F)}),
    where [F] is the formula in [solver].
    This is computed using [how].
    All variables [v] in [F] that are of integer type must be explicitly
    constrained in [F] to take on integer values only via [Int(v)].
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
    Integrality of integer-typed variables in [F] may be left implicit, i.e.,
    they do not have to be asserted via [Int(v)] in [F].
 *)
val convex_hull: abstraction_algorithm ->
                 ?man:(DD.closed Apron.Manager.t) ->
                 'a Syntax.context -> 'a Syntax.formula ->
                 ('a Syntax.arith_term) Array.t -> DD.closed DD.t

(** Relaxes the formula into one with no integrality constraints and where all
    variables are of type real, before taking the convex hull. *)
val convex_hull_of_real_relaxation:
  [`FullProject | `Lw] ->
  ?man:(DD.closed Apron.Manager.t) ->
  'a Syntax.context -> 'a Syntax.formula ->
  ('a Syntax.arith_term) Array.t -> DD.closed DD.t
