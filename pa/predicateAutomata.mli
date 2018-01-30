module type Alphabet = sig
  type t
  val pp : Format.formatter -> t -> unit
  val hash : t -> int
  val equal : t -> t -> bool

  module Set : sig
    type elt = t
    type t
    val mem : elt -> t -> bool
    val inter : t -> t -> t
    val diff : t -> t -> t
    val enum : t -> elt BatEnum.t
    val choose : t -> elt
    val is_empty : t -> bool
    val equal : t -> t -> bool
  end
end

module type Predicate = sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end

module type S = sig
  type t
  type predicate
  type letter
  type letter_set
  type formula = (predicate, int) PaFormula.formula
  type config

  module Config : Struct.S with type predicate = predicate
                            and type t = config

  module LetterSet : sig
    type t = letter_set
    val mem : letter -> t -> bool
    val inter : t -> t -> t
    val enum : t -> letter BatEnum.t
    val choose : t -> letter
  end

  val pp : Format.formatter -> t -> unit
  val pp_letter : Format.formatter -> letter -> unit

  (** [pp_ground size fmt a] formats the alternating finite automata obtained
      from the predicate automaton [a] by instantiating the universe to
      [size].  The printed format is the input format of the Alaska tool. *)
  val pp_ground : int -> Format.formatter -> t -> unit

  val pp_formula : Format.formatter -> formula -> unit

  (** [make alphabet vocabulary initial accepting] creates a new PA with
      alphabet [alphabet], vocabulary [vocabulary], initial formula [initial],
      and accepting predicates [accept].  Initially, the transition rule is
      defined to be [delta(q,a) = false] for all [(q,a)].  Transitions can be
      added using [add_transition]. *)
  val make : letter_set ->
    (predicate * int) list ->
    formula ->
    predicate list ->
    t

  (** [add_predicate pa p arity] destructively updates the PA [pa] by adding
      the predicate [p] to its vocabulary, with arity [arity] *)
  val add_predicate : t -> predicate -> int -> unit

  (** [add_accepting pa p] destructive updates the PA [pa] by making [p] an
      accepting predicate symbol *)
  val add_accepting : t -> predicate -> unit

  (** [add_transition pa q letters phi] destructively updates the PA [pa] by
      adding (for each [letter] in [letters]) the transition rule
      [delta(q,letter) = phi \/ psi], where [psi] was the previous transition
      rule for [(q,letter)]. *)
  val add_transition : t -> predicate -> letter_set -> formula -> unit

  (** [conjoin_transition pa q letters phi] destructively updates the PA [pa]
      by adding (for each [letter] in [letters]) the transition rule
      [delta(q,letter) = phi /\ psi], where [psi] was the previous transition
      rule for [(q,letter)]. *)
  val conjoin_transition : t -> predicate -> letter_set -> formula -> unit

  val alphabet : t -> letter_set

  (** [vocabulary pa] returns an enumeration of the predicate symbols used in
      [pa] along with their arity. *)
  val vocabulary : t -> (predicate * int) BatEnum.t

  (** [mem_vocabularity pa p] returns true iff [p] belongs to the vocabulary of
      [pa]. *)
  val mem_vocabulary : t -> predicate -> bool

  (** [arity pa p] returns the arity of the predicate [p].  If [p] does not
      belong to the vocabulary of [pa], raise [Not_found]. *)
  val arity : t -> predicate -> int

  val initial : t -> formula

  (** Compute the strongest post-condition of a formula under the transition
      relation corresponding to a given letter. *)
  val post : t -> formula -> letter -> formula

  (** Compute the strongest post-condition of a formula under the transition
      relation corresponding to a given indexed letter. *)
  val concrete_post : t -> formula -> (letter * int) -> formula

  val succs : t -> config -> (letter * int) -> config BatEnum.t

  (** [successors pa config index] computes a set of [index]-labeled
      successors of a configuration [config]. *)
  val successors : t -> config -> int -> (letter * config) BatEnum.t

  val pred : t -> config -> (letter * int) -> config

  (** [accepting_formula pa phi] determines whether all models of [phi] are
      accepting configurations of [pa]. *)
  val accepting_formula : t -> formula -> bool

  val accepting : t -> config -> bool

  val negate : t -> t
  val union : t -> t -> t
  val intersect : t -> t -> t
end

module Make (A : Alphabet) (P : Predicate) :
  S with type predicate = P.t
     and type letter = A.t
     and type letter_set = A.Set.t

module MakeEmpty (A : sig
    type t
    type letter
    type letter_set
    type config
    type predicate
    type formula = (predicate, int) PaFormula.formula
    module Config : Struct.S with type predicate = predicate
                              and type t = config
    module LetterSet : sig
      type t = letter_set
      val choose : t -> letter
    end
    val pp_letter : Format.formatter -> letter -> unit
    val alphabet : t -> letter_set
    val successors : t -> config -> int -> (letter * config) BatEnum.t
    val accepting : t -> config -> bool
    val initial : t -> formula
    val conjoin_transition : t -> predicate -> letter_set -> formula -> unit
    val add_transition : t -> predicate -> letter_set -> formula -> unit
    val add_predicate : t -> predicate -> int -> unit
    val add_accepting : t -> predicate -> unit
    val mem_vocabulary : t -> predicate -> bool
    val vocabulary : t -> (predicate * int) BatEnum.t
    val pp : Format.formatter -> t -> unit
  end) : sig
  type solver
  val pp : Format.formatter -> solver -> unit

  val mk_solver : A.t -> solver

  (** [conjoin_transition solver q sigma phi] adds destructively updates the
      PA in [solver] by adding the transition rule [delta(q,sigma) = phi /\
      psi], where [psi] was the previous transition rule for [(q,sigma)]. *)
  val conjoin_transition : solver ->
    A.predicate ->
    A.letter_set ->
    A.formula ->
    unit

  (** Add a predicate to the vocabulary of a solver.  Initially,
      [delta(q,sigma) = true] for all letters sigma. *)
  val add_predicate : solver -> A.predicate -> int -> unit

  (** Add a predicate to the vocabulary of a solver, and make it accepting.
      Initially, [delta(q,sigma) = true] for all letters sigma. *)
  val add_accepting_predicate : solver -> A.predicate -> int -> unit

  val mem_vocabulary : solver -> A.predicate -> bool

  val find_word : ?max_index:int -> solver -> ((A.letter * int) list) option

  val alphabet : solver -> A.letter_set
  val vocabulary : solver -> (A.predicate * int) BatEnum.t

  (** Parameter controlling the representation of configuration sets. *)
  val config_set_rep : [ `List | `PredicateTree | `FeatureTree ] ref

  (** Parameter controlling the backend of the structure embedding algorithm. *)
  val embed_set_algo : [ `MatchEmbeds | `CryptoMiniSat | `Lingeling | `HaifaCSP | `Gecode | `OrTools | `VF2] ref

  (** [bounded_empty pa bound] finds [Some] word which is accepted by [pa] and
      uses only indexed letters with index [<= bound]; [None] if there are no
      such words. *)
  val bounded_empty : A.t -> int -> ((A.letter * int) list) option

  val bounded_invariant : A.t ->
    int ->
    A.formula ->
    ((A.letter * int) list) option
end
