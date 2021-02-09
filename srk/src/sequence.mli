(** Infinite sequences *)

(** An ultimately periodic sequence is an infinite sequence consisting
   of a finite transient phase and an infinite periodic phase (with
   finite period).  *)
module UltimatelyPeriodic : sig
  type 'a t

  (** Pretty-print *)
  val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit

  (** Check if two ultimately periodic sequences are equal.  If the
     equality predicate is not supplied, it defaults to (=). *)
  val equal : ?equal:('a -> 'a -> bool) -> 'a t -> 'a t -> bool

  (** Enumerate the sequence. *)
  val enum : 'a t -> 'a BatEnum.t

  (** [map f s] constructs the sequence whose ith element is [f (s i)]
     *)
  val map : ('a -> 'b) -> 'a t -> 'b t

  (** [map f s1 s2] constructs the sequence whose ith element is [f
     (s1 i) (s2 i)] *)
  val map2 : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t

  (** [mapn f xs] constructs the sequence whose ith element is [f [(xs
     0) i; ..., (xs n) i]] *)
  val mapn : ('a list -> 'b) -> ('a t) list -> 'b t

  (** [make t p] constructs an ultimately periodic sequence with
     transient t and period p *)
  val make : 'a list -> 'a list -> 'a t

  (** Retrieve the transient part of a sequence *)
  val transient : 'a t -> 'a list

  (** Retrieve the periodic part of a sequence *)
  val periodic : 'a t -> 'a list

  (** Length of the period of a sequence *)
  val period_len : 'a t -> int

  (** Length of the transient part of a sequence *)
  val transient_len : 'a t -> int

  (** [nth s i] return (s i) *)
  val nth : 'a t -> int -> 'a

  (** Concatenate an ultimately periodic sequence to the end of a finite sequence *)
  val concat : 'a list -> 'a t -> 'a t

  (** Given a function [f] and an starting point [p], compute the
     sequence [p, f(p), f(f(p)), ...].  If this sequence is not
     ultimately periodic, [unfold] does not terminate.  If the
     equality predicate is not supplied, it defaults to (=). *)
  val unfold : ?equal:('a -> 'a -> bool) -> ('a -> 'a) -> 'a -> 'a t
end

(** A periodic sequence is an infinite sequence [s(0), s(1), s(2),
   ...] such that there is some period [p] such that [s(t) = s(t+p)]
   for all [t].  *)
module Periodic : sig
  type 'a t

  (** Pretty-print *)
  val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit

  (** Check if two ultimately periodic sequences are equal.  If the
     equality predicate is not supplied, it defaults to (=). *)
  val equal : ?equal:('a -> 'a -> bool) -> 'a t -> 'a t -> bool

  (** Enumerate the sequence. *)
  val enum : 'a t -> 'a BatEnum.t

  (** [make p] constructs the sequence of [p] repeated indefinitely *)
  val make : 'a list -> 'a t

  (** [map f s] constructs the sequence whose ith element is [f (s i)]
   *)
  val map : ('a -> 'b) -> 'a t -> 'b t

  (** [map f s1 s2] constructs the sequence whose ith element is [f
     (s1 i) (s2 i)] *)
  val map2 : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t

  (** [mapn f xs] constructs the sequence whose ith element is [f [(xs
     0) i; ..., (xs n) i]] *)
  val mapn : ('a list -> 'b) -> ('a t list) -> 'b t

  (** [nth s i] return (s i) *)
  val nth : 'a t -> int -> 'a

  (** Length of the period of a sequence *)
  val period_len : 'a t -> int

  (** Retrieve the period of a sequence *)
  val period : 'a t -> 'a list
end

(** Given an ultimately periodic sequence, find a periodic sequence
   that agrees with in on all but finitely many positions.  *)
val periodic_approx : 'a UltimatelyPeriodic.t -> 'a Periodic.t
