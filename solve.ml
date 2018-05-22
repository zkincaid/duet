(* Solve a max-plus recurrence *)

open Graph;;

(* Requisite types:
 *    weights: eventually GMP rationals; initially may be int; but, I do 
 *       need them to be allowed to be negative infinity
 *
 * Requisite data structures:
 *    Some numeric type...
 *    Matrix for input
 *        integer access, weight elements
 *    Digraph for matrix 
 *        Vertices have integers
 *        Edges have weight-type (eventually GMP rationals, I guess)
 *    Condensed (acyclic) digraph
 *        Vertices are addressed by integers
 *        Each vertex stands for a set of integers
 *        Edges are unweighted
 *
 *    Convenience data structures / operations:
 *         - map from components to contents
 *         - map from node to component ID
 *
 * Requisite operations:
 *    Compute a graph condensation:
 *    Topologically sort the strongly-connected components
 *    Find the ancestors of a component
 *    Find the descendants of a component
 *    Compute the simple cycles
 *
 * Better operations:
 *    Use a faster algorithm to compute slopes
 *)

type weight = Ninf | Fin of int;; (* eventually use GMP rationals *)

let wt_add w1 w2 = 
    match w1 with | Ninf -> Ninf | Fin v1 ->
        match w2 with | Ninf -> Ninf | Fin v2 -> Fin (v1 + v2)
;;

let wt_max w1 w2 = 
    match w1 with | Ninf -> w2 | Fin v1 ->
        match w2 with | Ninf -> w1 | Fin v2 -> Fin (max v1 v2)
;;

module V = struct
  type t = int (* vertex number *)
  let compare = Pervasives.compare
  let hash = Hashtbl.hash
  let equal = (=)
end;;
module E = struct
  type t = weight
  let compare = Pervasives.compare
  let default = Ninf
end;;

(* Max-plus recurrence graph *)
module MPGraph = Imperative.Graph.ConcreteLabeled(V)(E);;

module V2 = struct
  type t = int (* SCC number *)
  let compare = Pervasives.compare
  let hash = Hashtbl.hash
  let equal = (=)
end;;

module SCCGraph = Imperative.Graph.Concrete(V2);;

(* module MPGraph = Graph.Pack.Digraph;; *)

module Tests = struct
    module Knee1 = struct
        let matrix = [| [| (Fin 0);     Ninf;    Ninf    |];
                        [| (Fin (-14)); (Fin 3); Ninf    |];
                        [| Ninf;        (Fin 0); (Fin 1) |] |]
    end;;
end;;

let matrixToGraph matrix = 
    let graph = MPGraph.create () in
    let add_edges_in_row i row =
        let add_edge j wt = 
            match wt with | Ninf -> () | _ ->
            MPGraph.add_edge_e graph (MPGraph.E.create i wt j) in
        Array.iteri add_edge row in
    Array.iteri add_edges_in_row matrix
;;

module MPComponents = Graph.Components.Make(MPGraph);;

let karpMinimumCycleMean graph nComponents componentFromVertex = 
    let edge_weight i j = MPGraph.E.label (MPGraph.find_edge graph i j) in
    ()
;;

let createUpperBound graph = 
    let nVertices = MPGraph.nb_vertex graph in
    let (nComponents, componentFromVertex) = (MPComponents.scc graph) in
    let verticesFromComponent = Array.make nComponents [] in
    let rec makeVertexLists iVertex =
        if iVertex >= nVertices then () else 
            let iComponent = (componentFromVertex iVertex) in
            verticesFromComponent.(iComponent) <- iVertex :: verticesFromComponent.(iComponent)
    in makeVertexLists 0;
    let criticalWeight = Array.make nComponents Ninf in

    ()
;;

(*
let createUpperBound () = 
  (*  1. Construct a graph representation of the loop body matrix *) 
  (*  2. Compute the condensation of our graph *)
  (*  3. Compute critical circuit average weights (a.k.a. "critical weights") *)
  (*  4. Compute the bounding slopes: *)
  (*    First, initialize the values *)

  (*    The bounding slope in position (i,k) is the highest critical weight that is found    *)
  (*      in any circuit that is reachable from i and that can reach k.                      *)
  (*    So, we loop over each SCC (call it j),                                               *)
  (*      find all upstream SCCs (call each such i),                                         *)
  (*      and downstream SCCs (call each such k);                                            *)
  (*      then, what we have is (SCC_i) --*--> (SCC_j) --*--> (SCC_k)                        *)
  (*    Each time we find such a j, we update our slope for (i,k) to be j's critical weight  *)
  (*      if j's critical weight is greater than our current slope for (i,k).                *)
  (*  5. Compute the bounding intercepts (perform the "intercept propagation" steps)         *)

;;
*)



