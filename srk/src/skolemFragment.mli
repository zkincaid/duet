(** Skolem fragment from Algebraic Analysis for Maps.

    Currently supports only arrays with integer indices and elements,
    matching SRK's array support. *)
open Syntax

(** The correspondence produced by [project] and used by [lift]. Records
    the selected symbolic index and a mapping from array transition symbols and
    array-valued symbolic constants to integer symbols. *)
type correspondence

(** [project srk tf] returns [(correspondence, relation)].

    Each array state pair [(a, a')] becomes a pair of fresh integer state
    symbols. Each array-valued symbolic constant gets one fresh integer
    symbolic constant. Scalar state symbols, symbolic constants, and Skolem
    constants retain their roles.

    The body of [relation] is the original body conjoined with [z = a[j]]
    for every mapping entry [a -> z].
    The original arrays are existentially quantified through [TransitionFormula]'s
    [exists] predicate.

    The index [j] is represented as a symbolic constant, encoding the
    paper's [j = j'] constraint without introducing a separate post-state
    index [j']. *)
val project :
  'a context -> 'a TransitionFormula.t -> correspondence * 'a TransitionFormula.t

(** The integer symbol denoting the symbolic index. *)
val index : correspondence -> symbol

(** The integer symbol corresponding to an array transition symbol or
    array-valued symbolic constant. Returns [None] for symbols outside the
    mapping. *)
val mapped_symbol : correspondence -> symbol -> symbol option

(** [lift srk correspondence summary] replaces each mapped integer symbol [z]
    by the corresponding read [a[j]], then universally quantifies [j]. *)
val lift : 'a context -> correspondence -> 'a formula -> 'a formula
