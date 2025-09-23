open Symbolicheap
open Variable

type boogie_term = 
  Int of int
  | Var of boogie_var
  | Times of int * boogie_term
  | Sum of boogie_term * boogie_term
  | Read of boogie_avar * boogie_term

type boogie_formula = 
    Leq of boogie_term * boogie_term
  | Eq of boogie_term * boogie_term
  | AEq of boogie_avar * boogie_avar
  | And of boogie_formula * boogie_formula
  | Or of boogie_formula * boogie_formula
  | Not of boogie_formula
  | True

type boogie_instr = 
| Assign of boogie_var * boogie_term 
| AAssign of boogie_avar * boogie_avar 
| AWrite of boogie_avar * boogie_term * boogie_term 
| Assume of boogie_formula 
| Assert of boogie_formula 
| IteAssign of boogie_var * boogie_formula * boogie_term * boogie_term 
| Rotate of (boogie_avar * boogie_avar) list
| Return of boogie_term
| Error

module BGNode : sig
  type t = int * Llvmutil.LlvmNode.t * symbolicheap * boogie_instr list
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
end
module BGEdge : sig
  type t = boogie_formula option * boogie_instr list option
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val default : t
end

module BGraph : module type of Graph.Persistent.Digraph.ConcreteLabeled(BGNode)(BGEdge)

val boogie_term_of_int_term : int_term -> boogie_term 
val boogie_term_of_pointer_term : pointer_term -> boogie_term
val boogie_instr_text : boogie_instr -> string
val code_of_boogie_graph : BGNode.t -> BGraph.t -> boogie_var list -> boogie_avar list -> string

val generate_new_bvar : BGraph.t -> Variable.bvar
val build_graph : Boogie_ast.program -> BGraph.t

val graph_to_transition_system : BGraph.t -> Srk.TransitionSystem.Make(Global.Ctx)(Variable.Var)(Srk.Transition.Make(Global.Ctx)(Variable.Var)).t 