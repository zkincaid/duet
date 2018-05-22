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

type fweight = int;;  (* Finite weight. *) 
(* These are integers for now, but eventually we'll use GMP rationals *)

type weight = Ninf | Fin of fweight;;

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
  type t = fweight
  let compare = Pervasives.compare
  let default = 0
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
            match wt with | Ninf -> () | Fin fwt ->
            MPGraph.add_edge_e graph (MPGraph.E.create i fwt j) in
        Array.iteri add_edge row in
    Array.iteri add_edges_in_row matrix
;;

module MPComponents = Graph.Components.Make(MPGraph);;
module IntMap = Map.Make(struct type t = int let compare = compare end);;
module IntIntMap = Map.Make(struct type t = int * int let compare = compare end);;

let best x y = max x y;;
let worst x y = min x y;;

(* I chose Karp's algorithm because it was easy. *)
(*   We could use a faster alternative if time complexity becomes a concern. *)
let karpBestCycleMean graph nSCCs mapVertexToSCC mapSCCToVertices =
    (* Edges between SCCs are irrelevant, so we filter them out: *)
    let predecessors i =
        let unfiltered = MPGraph.pred graph i in
        List.filter (fun j -> ((mapVertexToSCC i) = (mapVertexToSCC j)))
                    unfiltered in
    let edge_weight i j = MPGraph.E.label (MPGraph.find_edge graph i j) in
    (* Loop over iSCC:, the SCC index *)
    let rec karpForSCC iSCC bestCycleMean =
        (* We run Karp's algorithm on one SCC, the one having number iSCC   *)
        if (iSCC >= nSCCs) then bestCycleMean else
        let vertices = mapSCCToVertices iSCC in 
        let nVertices = Array.length vertices in
        let startVertex = vertices.(0) in (* arbitrary start vertex *)
        let initialProgressions = Array.fold_left
            (fun initialProgressions iVertex -> IntIntMap.add 
                (0, iVertex)
                (if (iVertex = startVertex) then (Fin 0) else Ninf) 
                initialProgressions) IntIntMap.empty vertices in
        (* Loop over the number of steps in a progression (Karp's "k") *)
        let rec findProgressions steps bestProgression =
            (* Compute Karp's F_k(v) "minimum-weight edge progression." *)
            if (steps > nVertices) then bestProgression else
            (* let rec findProgressionsEachVertex iVertex *)
            (* MORE CODE HERE let bestProgression = ... *)
            (*
            (* Loop over v, the target vertex *)
            let bestProgression = Array.fold_left
                (fun newProgressions iVertex -> IntIntMap.add 
                    (steps, iVertex)
                    (if (iVertex = startVertex) then (Fin 0) else Ninf) 
                    newProgressions) bestProgression vertices in
            *)
            findProgressions (steps + 1) bestProgression in
        let bestProgression = findProgressions 1 initialProgressions in
        (* MORE CODE HERE let bestCycleMean = ... *)
        karpForSCC (iSCC + 1) bestCycleMean in
    let bestCycleMean = karpForSCC 0 IntMap.empty in
    ()
;;

let createUpperBound graph = 
    let nVertices = MPGraph.nb_vertex graph in
    let (nSCCs, mapVertexToSCC) = (MPComponents.scc graph) in
    let mapSCCToVertices = Array.make nSCCs [] in
    let rec makeVertexLists iVertex =
        if iVertex >= nVertices then () else 
            let iSCC = (mapVertexToSCC iVertex) in
            mapSCCToVertices.(iSCC) <- iVertex :: mapSCCToVertices.(iSCC)
    in makeVertexLists 0;
    let criticalWeight = Array.make nSCCs Ninf in
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



