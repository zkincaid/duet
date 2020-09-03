(* Constrainted horn clauses *)
open Syntax

type 'a chccontext = 
  { srk : 'a context;  relations : (string * typ list) BatDynArray.t}
type relation = int
type relation_atom = relation * symbol list
type 'a hypothesis = relation_atom list * 'a formula
type conclusion = relation_atom
type 'a clause = 'a hypothesis * conclusion


