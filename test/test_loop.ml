open Srk
open OUnit
open BatPervasives

module G = Graph.Persistent.Digraph.ConcreteBidirectional(SrkUtil.Int)
module L = Loop.Make(G)
module SCC = Graph.Components.Make(G)
module VS = L.VertexSet

let mk_graph edges =
  List.fold_left
    (fun g (u,v) -> G.add_edge g u v)
    G.empty
    edges

let is_acyclic graph =
  let scc = snd (SCC.scc graph) in
  G.fold_edges (fun u v acyclic ->
      acyclic && (scc u) != (scc v))
    graph
    true
  
(* Every cycle passes through a header *)
let feedback_vertex_set graph loop_nest =
  is_acyclic (L.VertexSet.fold
                (fun g v -> G.remove_vertex v g)
                (L.cutpoints loop_nest)
                graph)

(* Every loop is either disjoint or properly nested *)
let proper_nesting loop_nest =
  L.all_loops loop_nest
  |> BatList.enum
  |> SrkUtil.distinct_pairs
  |> BatEnum.for_all (fun (loop1, loop2) ->
         let b1, b2 = L.body loop1, L.body loop2 in
         VS.disjoint b1 b2 || VS.subset b1 b2 || VS.subset b2 b1)

(* Every loop is strongly connected *)
let loop_is_scc graph loop_nest =
  let scc = snd (SCC.scc graph) in
  L.all_loops loop_nest
  |> BatList.for_all (fun loop ->
         let scc_num = scc (VS.choose (L.body loop)) in
         VS.for_all (fun v -> scc v = scc_num) (L.body loop))

(* Loops contain their headers *)
let loop_contains_header loop_nest =
  L.all_loops loop_nest
  |> BatList.for_all (fun loop ->
         VS.mem (L.header loop) (L.body loop))

(* Test well-formedness conditions of Ramalingam criteria for "On
   Loops, Dominators, and Dominance Frontiers" (except undominance) *)
let well_formed graph loop_nest =
  assert_bool "Feedback vertex set" (feedback_vertex_set graph loop_nest);
  assert_bool "Proper nesting" (proper_nesting loop_nest);
  assert_bool "Loop is strongly connected" (loop_is_scc graph loop_nest);
  assert_bool "Loop contains header" (loop_contains_header loop_nest)

  
let suite = "Loop" >::: [
      "self_loop" >:: (fun () ->
        let g = mk_graph [(0, 1); (1, 1); (1, 2)] in
        well_formed g (L.loop_nest g)
      );

      "nested" >:: (fun () ->
        let g = mk_graph [(0, 1); (1, 2); (2, 3); (3, 1); (2, 4); (4, 2)] in
        well_formed g (L.loop_nest g)
      );

      "irreducible" >:: (fun () ->
        let g = mk_graph [(0, 1); (1, 2); (1, 3); (2, 3); (3, 2)] in
        well_formed g (L.loop_nest g)
      );

      (* Example from G. Ramalingam, "On Loops, Dominators, and
         Dominance Frontiers" *)
      "Ramalingam" >:: (fun () ->
        let g = mk_graph [(0, 1); (0, 2); (1, 3); (2, 4); (3, 5); (4, 5);
                          (3, 1); (4, 2); (3, 4); (4, 3)]
        in
        well_formed g (L.loop_nest g)
      );
  ]
