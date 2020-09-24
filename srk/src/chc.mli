(* Constrainted horn clauses *)
open Syntax

type 'b relcontext
type relation
type 'b relation_atom = relation * symbol list
type ('a, 'b) hypothesis = 'b relation_atom list * 'a formula
type ('a, 'b) rule = ('a, 'b) hypothesis * 'b relation_atom
type ('a, 'b) query = relation
type 'c rule_name
type 'c query_name
type ('a, 'b, 'c) chc

(*val parse_file : ?context:Z3.context -> 'a Syntax.context -> string -> 'a chc*)
(*val show_rel : relation -> string
val show_rel_atom : 'a context -> relation_atom -> string
val show_hypothesis : 'a context -> 'a hypothesis -> string
val show_conclusion : 'a context -> conclusion -> string
val show_rule : 'a context -> 'a rule -> string
val show_chc : 'a context -> 'a chc -> string
*)
val mk_relcontext : 'b relcontext
val pp_relation_atom : 
  'a context -> 'b relcontext -> Format.formatter -> 'b relation_atom -> unit
val pp_hypothesis : 
  'a context -> 'b relcontext -> Format.formatter -> ('a, 'b) hypothesis -> unit
val pp_rule : 
  'a context -> 'b relcontext -> Format.formatter -> ('a, 'b) rule -> unit
val pp_query : 
  'a context -> 'b relcontext -> Format.formatter -> ('a, 'b) query -> unit

val rel_sym_of : 'b relation_atom -> relation
val params_of : 'b relation_atom -> symbol list

module Relation : sig
  type t = relation
  module Set : BatSet.S with type elt = relation
  val compare : t -> t -> int
  val mk_relation : 'b relcontext -> ?name:string -> typ list -> relation
  val type_of : 'b relcontext -> relation -> typ list
  val name_of : 'b relcontext -> relation -> string
  val pp : 'b relcontext -> Format.formatter -> relation -> unit
end
module Chc : sig
  type ('a, 'b, 'c) t = ('a, 'b, 'c) chc
  val create : ?rlength:int -> ?qlength:int -> unit -> ('a, 'b, 'c) chc
  val copy : ('a, 'b, 'c) chc -> ('a, 'b, 'c) chc
  val add_rule : ('a, 'b, 'c) chc -> ('a, 'b) rule -> 'c rule_name
  val add_query : ('a, 'b, 'c) chc -> ('a, 'b) query -> 'c query_name
  val del_rule : ('a, 'b, 'c) chc -> 'c rule_name -> bool
  val del_query : ('a, 'b, 'c) chc -> 'c query_name -> bool
  val get_rules : ('a, 'b, 'c) chc -> ('c rule_name, ('a, 'b) rule) Hashtbl.t
  val get_queries :
    ('a, 'b, 'c) chc -> ('c query_name, ('a, 'b) query) Hashtbl.t
  val get_rule : ('a, 'b, 'c) chc -> 'c rule_name -> ('a, 'b) rule
  val get_query : ('a, 'b, 'c) chc -> 'c query_name -> ('a, 'b) query
  val upd_rule : ('a, 'b, 'c) chc -> 'c rule_name -> ('a, 'b) rule -> unit
  val upd_query : ('a, 'b, 'c) chc -> 'c query_name -> ('a, 'b) query -> unit
  val get_relations_used : ('a, 'b, 'c) chc -> Relation.Set.t
  val pp : 
    'a context -> 'b relcontext -> Format.formatter -> ('a, 'b, 'c) chc -> unit
  val is_linear : ('a, 'b, 'c) chc -> bool
end

module ChcSrkZ3 : sig
  val parse_z3fp : 
    ?z3queries:Z3.Expr.expr list -> 
    'a context -> 
    'b relcontext ->
    Z3.Fixedpoint.fixedpoint ->
    ('a, 'b, 'c) chc
  val parse_file :
    ?context:Z3.context ->
    'a context ->
    'b relcontext ->
    string -> 
    ('a, 'b, 'c) chc
  val parse_string :
    ?context:Z3.context ->
    'a context ->
    'b relcontext ->
    string -> 
    ('a, 'b, 'c) chc
end
(*val to_weighted_graph : 'a context -> 
  'a chc -> 
  (module Iteration.PreDomain) -> 
  (Syntax.symbol array * Syntax.symbol array * 'a Syntax.Formula.t) 
    WeightedGraph.t * int * int
*)
