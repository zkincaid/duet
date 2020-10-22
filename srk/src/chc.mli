(* Constrained horn clauses *)
open Syntax

type relcontext
type relation
type relation_atom
type 'a fp = {rules : (relation_atom list * 'a formula * relation_atom) list; 
              queries : relation list} 

(** Create fresh relation context *)
val mk_relcontext : relcontext

val pp_relation_atom : 'a context -> relcontext -> Format.formatter -> 
  relation_atom -> unit
val show_relation_atom : 'a context -> relcontext -> relation_atom -> string

(* Makes fresh relation symbol *)
val mk_relation : relcontext -> ?name:string -> typ list -> relation
val type_of : relcontext -> relation -> typ list
val name_of : relcontext -> relation -> string

(** This function includes typechecking. We hide the type of relation atoms 
 * to force the use to have their atom type checked *)
val mk_rel_atom : 'a context -> relcontext -> relation -> symbol list -> 
  relation_atom

val rel_of_atom : relation_atom -> relation
val params_of_atom : relation_atom -> symbol list



module Relation : sig
  type t = relation
  module Set : BatSet.S with type elt = relation
  val compare : t -> t -> int
  val pp : relcontext -> Format.formatter -> relation -> unit
  val show : relcontext -> relation -> string
end
module Fp : sig
  type 'a t = 'a fp
  (** Create chc with no rules/queries *)
  val create : 'a fp
  val add_rule : 'a fp -> relation_atom list -> 'a formula -> relation_atom -> 
    'a fp
  (** Adds query to chc and returns a fresh name for query *)
  val add_query : 'a fp -> relation -> 'a fp
  val get_relations_used : 'a fp -> Relation.Set.t
  val pp : 'a context -> relcontext -> Format.formatter -> 'a fp -> unit
  val show : 'a context -> relcontext -> 'a fp -> string
  (** [is_linear chc] returns true if chc is linear chc - that is, each
   * hypothesis has at most one relation atom *)
  val is_linear : 'a fp -> bool
  (** [check srk chc pd] returns unknown if a query relation can
   * be reached in the chc where recursion over-approximated using the 
   * star operator of the provided predomain [pd] and returns no otherwise.*)
  val check : 
    'a context -> 'a fp -> (module Iteration.PreDomain) -> 
    [> `No | `Unknown | `Yes]
  (** Solves a chc where recursion is over-approximated using the
   * star operator of the provided predomain [pd]. Where [f = solve srk chc pd]
   * and [r] is a relation used in [chc] the set of solutions to [r] is given by
   * [(syms, phi) = f r] where [phi] is a formula in which [syms.(i)]
   * gives the symbol used for the [i]th argument to [r].*)
  val solve : 'a context -> 'a fp -> (module Iteration.PreDomain) ->
    (relation -> symbol array * 'a formula)
end

module ChcSrkZ3 : sig
  (* Convert z3 fixedpoint into chc *)
  val parse_z3fp : ?z3queries:Z3.Expr.expr list -> 'a context -> 
    relcontext -> Z3.Fixedpoint.fixedpoint -> 'a fp
  val parse_file : ?context:Z3.context -> 'a context -> relcontext -> 
    string -> 'a fp
  val parse_string : ?context:Z3.context -> 'a context -> relcontext ->
    string -> 'a fp
end
