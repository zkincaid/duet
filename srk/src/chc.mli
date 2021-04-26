(* Constrained horn clauses *)
open Syntax

type relation
type rel_atom
type 'a fp = {mutable rules : (rel_atom list * 'a formula * rel_atom) list; 
              mutable queries : relation list;
              rel_ctx : (string * typ_fo list) BatDynArray.t} 

val pp_rel_atom : 'a context -> 'a fp -> Format.formatter -> rel_atom -> unit
val show_rel_atom : 'a context -> 'a fp -> rel_atom -> string

(* Makes fresh relation symbol *)
val mk_relation : 'a fp -> ?name:string -> typ_fo list -> relation
val type_of : 'a fp -> relation -> typ_fo list
val name_of : 'a fp -> relation -> string

(** This function includes typechecking. We hide the type of relation atoms 
 * to force the use to have their atom type checked *)
val mk_rel_atom : 'a context -> 'a fp -> relation -> symbol list -> rel_atom

val rel_of_atom : rel_atom -> relation
val params_of_atom : rel_atom -> symbol list

module Relation : sig
  type t = relation
  module Set : BatSet.S with type elt = relation
  val compare : t -> t -> int
  val pp : 'a fp -> Format.formatter -> relation -> unit
  val show : 'a fp -> relation -> string
end
module Fp : sig
  type 'a t = 'a fp
  (** Create fixed point object with no rules/queries *)
  val create : unit -> 'a fp
  val add_rule : 'a fp -> rel_atom list -> 'a formula -> rel_atom -> unit
  (** Adds query to fp and returns a fresh name for query *)
  val add_query : 'a fp -> relation -> unit
  (* Returns set of relations that occur in either a rule or query in fp *)
  val get_active_relations : 'a fp -> Relation.Set.t
  (* Returns list of all relations declared in fp context *)
  val get_relations_declared : 'a fp -> relation list
  val pp : 'a context -> Format.formatter -> 'a fp -> unit
  val show : 'a context  -> 'a fp -> string

  (* Limit each variable symbol to occur at most once as a parameter
   * in any given rule.
   *
   * For example, the rule R1(x) -> R2(x) is turned into R1(x) /\ x = x' => R2(x')
   *
   * Additionally quantifies over free vars in a constraint to that do not
   * appear as a parameter to a relation atom in the rule that constraint 
   * belongs to (that is, skolem constants will be unskomelized).
   *)
  val normalize : 'a context -> 'a fp -> 'a fp
  (* Creates an equivalent fp in which boolean parameters have been mapped to
   * integer parameters. Where [map, fp' = unbooleanize srk fp], the relation
   * [r] in [fp] is mapped to the relation symbol [map r] in [fp'].*)
  val unbooleanize : 'a context -> 'a fp -> (relation -> relation) * 'a fp
  (** [is_linear rules] returns true if rules defines linear system of chcs *)
  val is_linear : (rel_atom list * 'a formula * rel_atom) list -> bool
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
    (relation -> symbol array * 'a formula)
end

module ChcSrkZ3 : sig
  (* Convert z3 fixedpoint into srk fixedpoint *)
  val parse_z3fp : ?z3queries:Z3.Expr.expr list -> 'a context -> 'a fp -> 
    Z3.Fixedpoint.fixedpoint -> 'a fp
  val parse_file : ?ctx:Z3.context -> 'a context -> 'a fp -> string -> 'a fp 
  val parse_string : ?ctx:Z3.context -> 'a context -> 'a fp -> string -> 'a fp
end
