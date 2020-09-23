(* Constrainted horn clauses *)
open Syntax

type 'a chccontext 
type relation
type relation_atom = relation * symbol list
type 'a hypothesis = relation_atom list * 'a formula
type conclusion = relation_atom
type 'a rule = 'a hypothesis * conclusion
type 'a query = relation
type 'a chc = {rules : 'a rule list; queries : 'a query list}

val parse_file : ?context:Z3.context -> 'a Syntax.context -> string -> 'a chc
val show_rel : relation -> string
val show_rel_atom : 'a context -> relation_atom -> string
val show_hypothesis : 'a context -> 'a hypothesis -> string
val show_conclusion : 'a context -> conclusion -> string
val show_rule : 'a context -> 'a rule -> string
val show_chc : 'a context -> 'a chc -> string
val rel_sym_of : relation_atom -> relation
val params_of : relation_atom -> symbol list
val to_weighted_graph : 'a context -> 
  'a chc -> 
  (module Iteration.PreDomain) -> 
  (Syntax.symbol array * Syntax.symbol array * 'a Syntax.Formula.t) 
    WeightedGraph.t * int * int

