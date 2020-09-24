(* Constrainted horn clauses *)
open Syntax

type 'b relcontext
type relation
type ('a, 'b) relation_atom = relation * symbol list
type ('a, 'b) hypothesis = ('a, 'b) relation_atom list * 'a formula
type ('a, 'b) rule = ('a, 'b) hypothesis * ('a, 'b) relation_atom
type ('a, 'b) query = relation
type 'c rule_name
type 'c query_name
type ('a, 'b, 'c) chc

(** Create fresh relation context *)
val mk_relcontext : 'b relcontext

val pp_relation_atom : 'a context -> 'b relcontext -> Format.formatter -> 
  ('a, 'b) relation_atom -> unit
val pp_hypothesis : 'a context -> 'b relcontext -> Format.formatter -> 
  ('a, 'b) hypothesis -> unit
val pp_rule : 'a context -> 'b relcontext -> Format.formatter -> 
  ('a, 'b) rule -> unit
val pp_query : 'a context -> 'b relcontext -> Format.formatter -> 
  ('a, 'b) query -> unit
val show_relation_atom : 'a context -> 'b relcontext -> 
  ('a, 'b) relation_atom -> string
val show_hypothesis : 'a context -> 'b relcontext -> ('a, 'b) hypothesis -> 
  string
val show_rule : 'a context -> 'b relcontext -> ('a, 'b) rule -> string 
val show_query : 'a context -> 'b relcontext -> ('a, 'b) query -> string 


val rel_sym_of : ('a, 'b) relation_atom -> relation
val params_of : ('a, 'b) relation_atom -> symbol list

module Relation : sig
  type t = relation
  module Set : BatSet.S with type elt = relation
  val compare : t -> t -> int
  (** Create fresh relation symbol *)
  val mk_relation : 'b relcontext -> ?name:string -> typ list -> relation
  val type_of : 'b relcontext -> relation -> typ list
  val name_of : 'b relcontext -> relation -> string
  val pp : 'b relcontext -> Format.formatter -> relation -> unit
  val show : 'b relcontext -> relation -> string
end
module Chc : sig
  type ('a, 'b, 'c) t = ('a, 'b, 'c) chc
  (** Create chc with no rules/queries *)
  val create : ?rlength:int -> ?qlength:int -> unit -> ('a, 'b, 'c) chc
  val copy : ('a, 'b, 'c) chc -> ('a, 'b, 'c) chc
  (** Adds rule to chc and returns a fresh name for rule *)
  val add_rule : ('a, 'b, 'c) chc -> ('a, 'b) rule -> 'c rule_name
  (** Adds query to chc and returns a fresh name for query *)
  val add_query : ('a, 'b, 'c) chc -> ('a, 'b) query -> 'c query_name
  (** [del_rule chc rule_name] returns true and deletes [rule_name] from 
   * [chc] if [rule_name] exists in [chc]. Returns false otherwise *)
  val del_rule : ('a, 'b, 'c) chc -> 'c rule_name -> bool
  (** [del_query chc query_name] returns true and deletes [query_name] from 
   * [chc] if [query_name] exists in [chc]. Returns false otherwise *) 
  val del_query : ('a, 'b, 'c) chc -> 'c query_name -> bool
  val get_rules : ('a, 'b, 'c) chc -> ('c rule_name, ('a, 'b) rule) Hashtbl.t
  val get_queries : ('a, 'b, 'c) chc -> 
    ('c query_name, ('a, 'b) query) Hashtbl.t
  val get_rule : ('a, 'b, 'c) chc -> 'c rule_name -> ('a, 'b) rule
  val get_query : ('a, 'b, 'c) chc -> 'c query_name -> ('a, 'b) query
  (** [upd_rule chc rule_name rule] assigns [rule_name] in [chc] to [rule]. *)
  val upd_rule : ('a, 'b, 'c) chc -> 'c rule_name -> ('a, 'b) rule -> unit
  (** [upd_query chc query_name rule] assigns [query_name] in [chc] to [query].
    *)
  val upd_query : ('a, 'b, 'c) chc -> 'c query_name -> ('a, 'b) query -> unit
  (** Return all relation symbols used in chc *)
  val get_relations_used : ('a, 'b, 'c) chc -> Relation.Set.t
  val pp : 'a context -> 'b relcontext -> Format.formatter -> 
    ('a, 'b, 'c) chc -> unit
  val show : 'a context -> 'b relcontext -> ('a, 'b, 'c) chc -> string
  (** [is_linear chc] returns true if chc is linear chc - that is, each
   * hypothesis has at most one relation atom *)
  val is_linear : ('a, 'b, 'c) chc -> bool
  (** [has_reachable_goal srk chc pd] returns yes if a query relation can
   * be reached in the chc where... TODO: come up with better comment *)
  val has_reachable_goal : 
    'a context -> 
    ('a, 'b, 'c) chc -> 
    (module Iteration.PreDomain) ->
    [> `No | `Unknown | `Yes ]
end

module ChcSrkZ3 : sig
  (* Convert z3 fixedpoint into chc *)
  val parse_z3fp : ?z3queries:Z3.Expr.expr list -> 'a context -> 
    'b relcontext -> Z3.Fixedpoint.fixedpoint -> ('a, 'b, 'c) chc
  val parse_file : ?context:Z3.context -> 'a context -> 'b relcontext -> 
    string -> ('a, 'b, 'c) chc
  val parse_string : ?context:Z3.context -> 'a context -> 'b relcontext ->
    string -> ('a, 'b, 'c) chc
end
