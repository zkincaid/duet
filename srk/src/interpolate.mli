(** Interpolation of transition formulas. *)
open Syntax 

module StdInterpolate
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
        val show : t -> string

        (** Guarded parallel assignment *)
        val construct : C.t formula -> (var * C.t arith_term) list -> t

        (** [assume phi] is a transition that doesn't modify any variables, but can
            only be executed when [phi] holds *)
        val assume : C.t formula -> t

        (** [assign v t] is a transition that assigns the term [t] to the variable
            [v]. *)
        val assign : var -> C.t arith_term -> t

        (** Parallel assignment of a list of terms to a list of variables.
            If a variable appears multiple times as a target for an
            assignment, the rightmost assignment is taken. *)
        val parallel_assign : (var * C.t arith_term) list -> t

        (** Assign a list of variables non-deterministic values. *)
        val havoc : var list -> t

        (** Sequentially compose two transitions. *)
        val mul : t -> t -> t

        (** Non-deterministically choose between two transitions *)
        val add : t -> t -> t

        (** take conjunction of two transition formulas *)
        val conjunct : t -> t -> t

        (** Unexecutable transition (unit of [add]). *)
        val zero : t

        (** Skip (unit of [mul]). *)
        val one : t

        (** [exists ex tr] removes the variables that do not satisfy the predicate
            [ex] from the footprint of a transition.  For example, projecting a
            variable [x] out of a transition [tr] is logically equivalent to
            [(exists x. tr) && x' = x]. *)
        val exists : (var -> bool) -> t -> t

        val is_zero : t -> bool
        val is_one : t -> bool

        (** Retrieve the value of a variable after a transition as a term over input
            variables (and Skolem constants) *)
        val get_transform : var -> t -> C.t arith_term

        (** Enumerate the variables and values assigned in a transition. *)
        val transform : t -> (var * C.t arith_term) BatEnum.t

        (** The condition under which a transition may be executed. *)
        val guard : t -> C.t formula

        (**  
            transtion : guard, transform
            interpretation: M
            find a model of the guard where we use M to replace all the pre-state value.
            check interpretation.substitute 
        *)
        val get_post_model : C.t Interpretation.interpretation -> t -> (C.t Interpretation.interpretation) option 


        (** Underapproximate existential quantification using model-based projection. 
            The variables to be preserved are set to `true` in the initial map. 
            Note the input map specifies variables to be preserved, not removed. *)
        val project_mbp : (var -> bool) -> t -> [> `Sat of t | `Unsat]


        (** Given a pre-condition [P], a path [path], and a post-condition [Q],
            determine whether the Hoare triple [{P}path{Q}] is valid. *)
        val valid_triple : C.t formula -> t list -> C.t formula -> [ `Valid
                                                                    | `Invalid
                                                                    | `Unknown ]

        val contains_havoc : t -> bool


        val defines : t -> var list
        val uses : t -> var list

        val abstract_post : (C.t,'abs) SrkApron.property -> t -> (C.t,'abs) SrkApron.property

        (** Compute a representation of a transition as a transition formula. *)
        val to_transition_formula : t -> C.t TransitionFormula.t

        val domain : (C.t Iteration.exp_op) ref
        val star : t -> t
        val linearize : t -> t

        (** If [is_deterministic tr] holds, [tr] is deterministic (at most one
            post-state for any given pre-state).  If [is_deterministic tr] does not
            hold, either [tr] is non-deterministic, or a proof of determinacy could
            not be found. *)
        val is_deterministic : t -> bool


        (** vocabulary of a transition formula, (globals, locals)*)
        val vocabulary : t -> ((Syntax.symbol list) * (Syntax.symbol list))
end) : sig 


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
