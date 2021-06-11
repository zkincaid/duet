(* Constrained horn clauses *)
open Syntax

type proposition
type 'a fp 

module Proposition : sig
  type t = proposition
  val symbol_of : t -> symbol
  val names_of : t -> string list
  val typ_of_params : 'a context -> t -> typ_fo list
  val mk_proposition : 'a context -> symbol -> string list -> t
end
module Fp : sig
  type 'a t = 'a fp
  (** Create fixed point object with no rules/queries *)
  val empty : 'a fp
  val add_rule : 'a fp -> proposition -> proposition list -> 'a formula -> 'a fp
  (** Adds query to fp and returns a fresh name for query *)
  val add_query : 'a fp -> symbol -> 'a fp
  (* Returns set of relations that occur in either a rule or query in fp *)
  (*val predicate_symbols : 'a fp -> Symbol.Set.t*)
  val pp : 'a context -> Format.formatter -> 'a fp -> unit
  val show : 'a context  -> 'a fp -> string

  (** [check srk fp pd] returns unknown if a query relation can
   * be reached in the fp where recursion over-approximated using the 
   * star operator of the provided predomain [pd] and returns no otherwise.*)
  val check : 
    'a context -> 'a fp -> (module Iteration.PreDomain) -> 
    [> `No | `Unknown | `Yes]
  (** [query_vc_condition srk fp pd] returns the final vc condition used in
   * [check srk fp pd]. That is, the vc condition to determine whether a query
   * relation can be reached in the fp where recursion over-approximated using 
   * the star operator of the provided predomain [pd].*)
  val query_vc_condition : 
    'a context -> 'a fp -> (module Iteration.PreDomain) -> 'a formula 
  (** Solves a fp where recursion is over-approximated using the
   * star operator of the provided predomain [pd]. Where [f = solve srk fp pd]
   * and [r] is a relation used in [fp] the set of solutions to [r] is given by
   * [(syms, phi) = f r] where [phi] is a formula in which [syms.(i)]
   * gives the symbol used for the [i]th argument to [r].*)
  val solve : 'a context -> 'a fp -> (module Iteration.PreDomain) ->
    (int -> 'a formula)
end

module ChcSrkZ3 : sig
  (* Convert z3 fixedpoint into srk fixedpoint *)
  val parse_z3fp : ?z3queries:Z3.Expr.expr list -> 'a context  -> 
    Z3.Fixedpoint.fixedpoint -> 'a fp
  val parse_file : ?ctx:Z3.context -> 'a context -> string -> 'a fp 
  val parse_string : ?ctx:Z3.context -> 'a context -> string -> 'a fp
end
