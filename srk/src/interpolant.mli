(** Interpolation of transition formulas. *)
open Syntax 

module type Interpolant = functor 
    (C: sig 
        type t 
        val context : t context 
    end)
    (V: sig
        type t
        val show : t -> string
        val typ : t -> [ `TyInt | `TyReal ]
        val compare : t -> t -> int
        val symbol_of : t -> symbol
        val of_symbol : symbol -> t option
        val is_global : t -> bool
    end)
    (T: sig 
        type t
        type var = V.t
        val equal : t -> t -> bool
        val compare : t -> t -> int

        (** Guarded parallel assignment *)
        val construct : C.t formula -> (var * C.t arith_term) list -> t

        val create : C.t formula -> (var * C.t arith_term) BatEnum.t -> t 
        (** [exists ex tr] removes the variables that do not satisfy the predicate
            [ex] from the footprint of a transition.  For example, projecting a
            variable [x] out of a transition [tr] is logically equivalent to
            [(exists x. tr) && x' = x]. *)
        val exists : (var -> bool) -> t -> t

        (** (Needed by interpolation) *)
        val destruct_and : (C.t context) -> (C.t formula) -> (C.t formula) list

        (** Enumerate the variables and values assigned in a transition. *)
        val transform : t -> (var * C.t arith_term) BatEnum.t

        (** The condition under which a transition may be executed. *)
        val guard : t -> C.t formula
  end) -> sig 


      (** Given a path (list of transitions [tr_1 ... tr_n]) and a post-condition
      formula, determine whether the path implies the post-condition.  If yes,
      return a sequence of intermediate assertions [phi_1 ... phi_n] that
      support the proof (for each [i], [{ phi_{i-1} } tr_i { phi_i }] holds,
      where [phi_0] is [true] and [phi_n] implies the post-condition). *)

      val interpolate : T.t list -> C.t formula -> [ `Valid of C.t formula list
      | `Invalid
      | `Unknown ]


      (** Same as interpolate, but returns a concrete model if interpllation fails. *)
      val interpolate_or_concrete_model : T.t list -> C.t formula 
        -> [`Valid of C.t formula list 
        | `Invalid of C.t Interpretation.interpretation 
        | `Unknown ]
end
