(* Constrainted horn clauses *)
open Syntax

type relcontext
type relation
type relation_atom
type 'a hypothesis = relation_atom list * 'a formula
type 'a rule = 'a hypothesis * relation_atom
type query = relation
type 'a chc = {rules : 'a rule list; queries : query list} 

(** Create fresh relation context *)
val mk_relcontext : relcontext

val pp_relation_atom : 'a context -> relcontext -> Format.formatter -> 
  relation_atom -> unit
val pp_hypothesis : 'a context -> relcontext -> Format.formatter -> 
  'a hypothesis -> unit
val pp_rule : 'a context -> relcontext -> Format.formatter -> 'a  rule -> unit
val pp_query : relcontext -> Format.formatter -> query -> unit
val show_relation_atom : 'a context -> relcontext -> relation_atom -> string
val show_hypothesis : 'a context -> relcontext -> 'a hypothesis -> string
val show_rule : 'a context -> relcontext -> 'a rule -> string 
val show_query : relcontext -> query -> string 

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

val mk_hypo : relation_atom list -> 'a formula -> 'a hypothesis
val mk_rule : 'a hypothesis -> relation_atom -> 'a rule



module Relation : sig
  type t = relation
  module Set : BatSet.S with type elt = relation
  val compare : t -> t -> int
  val pp : relcontext -> Format.formatter -> relation -> unit
  val show : relcontext -> relation -> string
end
module Chc : sig
  type 'a t = 'a chc
  (** Create chc with no rules/queries *)
  val create : 'a chc
  val chc_of : 'a rule list -> query list -> 'a chc
  val add_rule : 'a chc -> 'a rule -> 'a chc
  (** Adds query to chc and returns a fresh name for query *)
  val add_query : 'a chc -> query -> 'a chc
  val get_rules : 'a chc -> 'a rule list
  val get_queries : 'a chc -> query list 
  val get_relations_used : 'a chc -> Relation.Set.t
  val pp : 'a context -> relcontext -> Format.formatter -> 'a chc -> unit
  val show : 'a context -> relcontext -> 'a chc -> string
  (** [is_linear chc] returns true if chc is linear chc - that is, each
   * hypothesis has at most one relation atom *)
  val is_linear : 'a chc -> bool
  (** [has_reachable_goal srk chc pd] returns unknown if a query relation can
   * be reached in the chc where recursion over-approximated using the 
   * star operator of the provided predomain [pd] and returns no otherwise.*)
  val has_reachable_goal : 
    'a context -> 'a chc -> (module Iteration.PreDomain) -> [> `No | `Unknown]
  (** Solves a chc where recursion is over-approximated using the
   * star operator of the provided predomain [pd]. Where [f = solve srk chc pd]
   * and [r] is a relation used in [chc] the set of solutions to [r] is given by
   * [(syms, phi) = f r] where [phi] is a formula in which [syms.(i)]
   * gives the symbol used for the [i]th argument to [r].*)
  val solve : 'a context -> 'a chc -> (module Iteration.PreDomain) ->
    (relation -> symbol array * 'a formula)
end

module ChcSrkZ3 : sig
  (* Convert z3 fixedpoint into chc *)
  val parse_z3fp : ?z3queries:Z3.Expr.expr list -> 'a context -> 
    relcontext -> Z3.Fixedpoint.fixedpoint -> 'a chc
  val parse_file : ?context:Z3.context -> 'a context -> relcontext -> 
    string -> 'a chc
  val parse_string : ?context:Z3.context -> 'a context -> relcontext ->
    string -> 'a chc
end
