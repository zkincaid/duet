open Variable 

module LlvmNode :
  sig
    type t 
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val hash : t -> int
    val name : t -> string
    val llvm_identifier : t -> int
    val llvm_block : t -> Llvm.llbasicblock
    val phi_num : t -> int
  end

val dummy : LlvmNode.t

val llvm_block_to_string : Llvm.llbasicblock -> string
val block_eq : Llvm.llbasicblock -> Llvm.llbasicblock -> bool
val block_id : Llvm.llbasicblock -> int
val generate_llvm_ir : string -> Llvm.llmodule
val generate_llvm_graph_from_ir : Llvm.llmodule -> Graph.Persistent.Digraph.Concrete(LlvmNode).t * LlvmNode.t * (all_var list)
val generate_llvm_graph : string -> Graph.Persistent.Digraph.Concrete(LlvmNode).t * LlvmNode.t * (all_var list)
val print_llvm_block : Llvm.llbasicblock -> unit

val is_malloc : Llvm.llvalue -> bool
val is_free : Llvm.llvalue -> bool
