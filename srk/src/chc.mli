(* Constrainted horn clauses *)
open Syntax

type relcontext
type relation
type relation_atom
type 'a hypothesis
type 'a rule
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

val mk_rel_atom : 'a context -> relcontext -> relation -> symbol list -> 
  relation_atom

(** Creates a relation atom with a fresh relation using the
 * symbols provided as the atoms arguments *)
val mk_rel_atom_fresh : 'a context -> relcontext -> ?name:string ->
  symbol list -> relation_atom

(** [mk_n_rel_atoms_fresh srk rel_ctx name syms n] calls 
 * [mk_rel_atom_fresh srk rel_ctx name syms] n times and returns the result.
 * That is, creates n relation atoms with same name and parameters but with
 * unique relation symbols *)
val mk_n_rel_atoms_fresh : 'a context -> relcontext -> ?name:string ->
  symbol list -> int -> relation_atom array

val rel_of_atom : relation_atom -> relation
val params_of_atom : relation_atom -> symbol list

(** [postify_atom trs rel_atom] substitutes the parameters of rel_atom
 * with their post relation symbols in trs *)
val postify_atom : (symbol * symbol) list -> relation_atom -> relation_atom

(** [preify_atom trs rel_atom] substitutes the parameters of rel_atom
 * with their pre relation symbols in trs *)
val preify_atom : (symbol * symbol) list -> relation_atom -> relation_atom



val mk_hypo : relation_atom list -> 'a formula -> 'a hypothesis
val mk_rule : 'a hypothesis -> relation_atom -> 'a rule
(** shorthand for mk_rule with no relations in hypothesis *)
val mk_fact : 'a formula -> relation_atom -> 'a rule



(** [mk_mapped_rule trs hypo_atoms phi conc] creates a rule in which 
 * [preify_atom trs atom] is called for each atom in hypo_atoms and 
 * [postify_atom trs conc] is called for the conclusion atom. In short, the
 * parameters in the hypothesis atoms and "preified" 
 * and the paramters in the conclusion atom are "postified".*)
val mk_mapped_rule : (symbol * symbol) list -> relation_atom list -> 
  'a formula -> relation_atom -> 'a rule

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
  (** [has_reachable_goal srk chc pd] returns yes if a query relation can
   * be reached in the chc where recursion over-approximated using the 
   * star operator of the provided predomain *)
  val has_reachable_goal : 
    'a context -> 'a chc -> (module Iteration.PreDomain) -> [> `No | `Unknown]
  (** Solves a chc where recursion is over-approximated using the
   * star operator of the provided predomain*)
  val solve : 'a context -> 'a chc -> (module Iteration.PreDomain) ->
    (relation -> 'a formula)
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
