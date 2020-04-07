(** Calculating a loop nesting forest.  *)

(* Signature of a loop record *)
type 'a loops =
  { 
    (* loop header vertex *)
    header: WeightedGraph.vertex; 
    (* after the header is split into 2 vertices, recording the new vertex created *)
    splitted_hd: WeightedGraph.vertex; 
    (* vertices belong to this loop *)
    loop_body_vertices: WeightedGraph.vertex list; 
    (* an edge from within the loop body to its header *)
    back_edge: WeightedGraph.vertex * WeightedGraph.vertex * 'a; 
    (* largest loops nested inside this loop *)
    children: 'a loops list; 
    (* depth in the loop-nesting forest *)
    depth: int; 
    (* formula representing all paths from a chosen start point to the loop header *)
    header_f: 'a; 
    (* formula representing one iteration of the loop *)
    body_f: 'a; 
  }

(* log a loop *)
val print_loop: 'a loops -> unit

(**  Construct a loop nesting forest for a weighted graph, returns a list of 
top-level parent loops, and a flattened list of all loops in the graph consisting
only of their header and body formulas  *)
val compute_all_nested_loops: 'a WeightedGraph.t -> WeightedGraph.vertex -> 'a loops list * ('a * 'a) list
