(** Wedge abstract domain.  A wedge corresponds to a conjunction of equations
    and inequations over a vocabulary that includes addition, multiplication,
    exponentiation, logarithm, division, and modulo. *)
open Syntax

type 'a t

val pp : Format.formatter -> 'a t -> unit

val show : 'a t -> string

val join : ?lemma:('a formula -> unit) -> 'a t -> 'a t -> 'a t

val meet : 'a t -> 'a t -> 'a t

val meet_atoms : 'a t -> ('a formula) list -> unit

val equal : 'a t -> 'a t -> bool

val widen : 'a t -> 'a t -> 'a t

val of_atoms : 'a context ->
  ('a formula) list ->
  'a t

val to_atoms : 'a t -> ('a formula) list

val to_formula : 'a t -> 'a formula

(** Project symbols out of a wedge that do not satisfy the given predicate.
    Additionally project out terms that contain a symbol that does not satisfy
    the subterm predicate. *)
val exists : ?lemma:('a formula -> unit) ->
  ?subterm:(symbol -> bool) ->
  (symbol -> bool) ->
  'a t ->
  'a t

val top : 'a context -> 'a t

val bottom : 'a context -> 'a t

val is_bottom : 'a t -> bool

val is_top : 'a t -> bool

(** Compute a representation of the set of equalities that are entailed by a
    given wedge as a list [(term0, vector0),...,(termn,vectorn)].  The
    interpretation of this representation is that for any vector v,
    [wedge |= (vector0 . v) term0 + ... + (vectorn . v) termn = 0]
    where [.] represents the dot product. *)
val farkas_equalities : 'a t -> ('a arith_term * Linear.QQVector.t) list

(** Given a wedge [wedge] and a symbol [symbol], compute a list of lower bounds
    and upper bounds for [symbol] that are implied by [wedge]. *)
val symbolic_bounds : 'a t -> symbol -> ('a arith_term) list * ('a arith_term) list

(** Given a wedge [wedge] and a term [term], compute a lower and upper bounds
    for [term] within the region [wedge]. *)
val bounds : 'a t -> 'a arith_term -> Interval.t

(** Ensure that a context has named [max] and [min] symbols.  If the symbols
    are not present in the context [ensure_max_min] registers them. *)
val ensure_min_max : 'a context -> unit

(** Compute a wedge that over-approximates a given formula *)
val abstract : ?exists:(symbol -> bool) ->
  ?subterm:(symbol -> bool) ->
  'a context ->
  'a formula ->
  'a t

(** Compute a set of equations that are entailed by a given formula *)
val abstract_equalities : ?exists:(symbol -> bool) ->
  ?subterm:(symbol -> bool) ->
  'a context ->
  'a formula ->
  'a t

(** A subwedge is an abstract domain that can be associated with a
   sublattice of the disjunctive completion of the lattice of wedges
   (see [abstract_subwedge]).  The [of_wedge] and [join] functions
   come with a [lemma] parameter, which a subwedge domain is
   responsible for invoking for each theory lemma that is not provable
   in linear arithmetic. A safe (but inefficient) method for ensuring
   safety is to call
    lemma ((Wedge.to_formula in) => (subwedge.to_formula out))
   in [of_wedge] and
    lemma ((Wedge.to_formula in1) => (subwedge.to_formula out))
    lemma ((Wedge.to_formula in2) => (subwedge.to_formula out))
   in [join]. *)
type ('a, 'b) subwedge =
  { of_wedge : lemma:('a formula -> unit) -> 'a t -> 'b;
    join : lemma:('a formula -> unit) -> 'b -> 'b -> 'b;
    to_formula : 'b -> 'a formula }

(** Compute a subwedge that over-approximates a given formula.  This
   is typically faster than using [abstract] to compute an
   over-approximating wedge and then *)
val abstract_subwedge :
  ('a, 'b) subwedge ->
  ?exists:(symbol -> bool) ->
  ?subterm:(symbol -> bool) ->
  'a context ->
  'a formula ->
  'b

(** Check if a formula is satisfiable by computing an over-approximating wedge
    and checking whether it is feasible.  This procedure improves on the naive
    implementation by returning [`Unknown] as soon as it finds a disjunct that
    it can't prove to be infeasible.  *)
val is_sat : 'a context -> 'a formula -> [ `Sat | `Unsat | `Unknown ]

(** Compute lower and upper bounds for a symbol that are implied by the given
    formula (if they exist).  The upper and lower bounds may involve only
    symbols that satisfy the exist predicate, and may involve the functions
    [max] and [min] (binary named symbols).  (For example, if [x] is bounded
    above by [0] and [y], then the upper bound computed by [symbolic_bounds]
    is [min(0,y)]). *)
val symbolic_bounds_formula : ?exists:(symbol -> bool) ->
  'a context ->
  'a formula ->
  symbol ->
  [ `Sat of (('a arith_term) option * ('a arith_term) option) | `Unsat ]

(** As [symbolic_bounds_formula], execept the lower bound is
   represented as a min of maxes, and the upper bound is represented
   as a max of mins. *)
val symbolic_bounds_formula_list : ?exists:(symbol -> bool) ->
  'a context ->
  'a formula ->
  symbol ->
  [ `Sat of (('a arith_term) list list) * (('a arith_term) list list) | `Unsat ]

val coordinate_system : 'a t -> 'a CoordinateSystem.t

val polyhedron : 'a t -> ([ `Eq | `Geq ] * Linear.QQVector.t) list

val vanishing_ideal : 'a t -> Polynomial.QQXs.t list

val copy : 'a t -> 'a t

val equational_saturation : ?lemma:('a formula -> unit) -> 'a t -> Polynomial.Rewrite.t

val strengthen : ?lemma:('a formula -> unit) -> 'a t -> unit

(** Simplify the constraint represenation of the given wedge.  The
   resulting wedge is equivalent the input, modulo LIRA + the lemmas
   passed to the lemma procedure. *)
val reduce : lemma:('a formula -> unit) -> 'a t -> 'a t

(** Overapproximate existential quantifier elimination. *)
val cover : ?subterm:(symbol -> bool) ->
  'a context ->
  (symbol -> bool) ->
  'a formula ->
  'a formula
