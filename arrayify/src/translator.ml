open Variable

module Heap = Set.Make(Symbolicheap.HeapElem)

module GLlvm =  Graph.Persistent.Digraph.Concrete(Llvmutil.LlvmNode)
module GBoogie = Graph.Persistent.Digraph.ConcreteLabeled(Boogieir.BGNode)(Boogieir.BGEdge)

module DotLlvm = Graph.Graphviz.Dot(struct
   include GLlvm (* use the graph module from above *)
   let graph_attributes _ = []
    let default_vertex_attributes _ = []
    let vertex_name v = (Llvmutil.LlvmNode.name v)
    let vertex_attributes _ = [`Shape `Box]
    let get_subgraph _ = None
    let default_edge_attributes _ = []
    let edge_attributes _ = []
end)

module DotBoogie = Graph.Graphviz.Dot(struct
  include GBoogie
  let graph_attributes _ = []
  let default_vertex_attributes _ = []
  let vertex_name (id, v, _, _) = "n"^string_of_int id ^ "q" ^ (Llvmutil.LlvmNode.name v) 
  let vertex_attributes (_, _, _, _) = 
    [`Shape `Box]
  let get_subgraph _ = None
  let default_edge_attributes _ = []
  let edge_attributes _ = []


end)

let translate fn precondition =
  let llvm_graph, entry, params = Llvmutil.generate_llvm_graph fn in
  let oc = open_out "/Users/np6641/dev/arrayify/llvmgraph.dot" in
  DotLlvm.output_graph oc llvm_graph; print_string "Graph written to llvmgraph.dot\n";
  close_out oc;
  let boogie_graph, boogie_entry = Executor.execute entry llvm_graph precondition in
  let oc = open_out "/Users/np6641/dev/arrayify/myboogiegraph.dot" in
  DotBoogie.output_graph oc boogie_graph; print_string "Graph written to myboogiegraph.dot\n";
  close_out oc;
  GBoogie.iter_vertex (fun (id, v, sh, _) -> 
    print_string ("Vertex: " ^ string_of_int id ^ " " ^ Llvmutil.LlvmNode.name v ^ " " ^ Symbolicheap.string_of_symbolicheap sh ^ "\n")) boogie_graph;
  let boogie_params = List.map (fun v -> 
    match v with
    | Variable v -> boogie_var_of_var v
    | Pointer v -> boogie_var_of_pvar v
    | Block _ -> assert false
  ) params in
  let array_params = Heap.fold (fun e acc -> 
    match e with 
    | Array b -> (boogie_avar_of_bvar b) :: acc
    | TrueHeap -> acc
    ) (snd precondition) [] in 
  let boogie_code = Boogieir.code_of_boogie_graph boogie_entry boogie_graph boogie_params array_params in
  let oc = open_out "/Users/np6641/dev/arrayify/output.bpl" in
  output_string oc boogie_code; print_string boogie_code;
  close_out oc