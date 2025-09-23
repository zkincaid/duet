open Symbolicheap
open Llvmutil
open Boogieir

val execute : LlvmNode.t -> Graph.Persistent.Digraph.Concrete(LlvmNode).t -> symbolicheap -> Graph.Persistent.Digraph.ConcreteLabeled(BGNode)(BGEdge).t * BGNode.t