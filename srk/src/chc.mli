(* Constrainted horn clauses *)
open Syntax

type 'a chccontext 
type relation
type 'a relation_atom = relation * 'a term list
type 'a hypothesis = 'a relation_atom list * 'a formula
type 'a conclusion = 'a relation_atom
type 'a clause = 'a hypothesis * 'a conclusion
type 'a chc = 'a clause list

val parse_file : ?context:Z3.context -> 'a Syntax.context -> string -> 'a chc
val show_rel : relation -> string
val show_rel_atom : 'a context -> 'a relation_atom -> string
val show_hypothesis : 'a context -> 'a hypothesis -> string
val show_conclusion : 'a context -> 'a conclusion -> string
val show_clause : 'a context -> 'a clause -> string
val show_chc : 'a context -> 'a chc -> string
