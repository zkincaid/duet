(* Constrainted horn clauses *)
open Syntax

type 'a chccontext 
type relation
type relation_atom = relation * symbol list
type 'a hypothesis = relation_atom list * 'a formula
type conclusion = relation_atom
type 'a rule = 'a hypothesis * conclusion
type 'a query = 'a hypothesis
type 'a chc = {rules : 'a rule list; queries : 'a query list}

val parse_file : ?context:Z3.context -> 'a Syntax.context -> string -> 'a chc
val show_rel : relation -> string
val show_rel_atom : 'a context -> relation_atom -> string
val show_hypothesis : 'a context -> 'a hypothesis -> string
val show_conclusion : 'a context -> conclusion -> string
val show_rule : 'a context -> 'a rule -> string
val show_chc : 'a context -> 'a chc -> string

module LinCHC : sig
  type 'a linhypo = relation_atom option * 'a formula
  type 'a linrule = 'a linhypo * conclusion
  type 'a linquery = 'a linhypo
  type 'a linchc = {rules : 'a linrule list; queries : 'a linquery list}
  val to_weighted_graph : 'a context -> 
    'a linchc -> 
    (module Iteration.PreDomain) -> 
    'a WeightedGraph.t
end
