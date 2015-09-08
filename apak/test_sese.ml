open BatPervasives
open Putil
open OUnit
open RecGraph

module G = struct
  include Graph.Persistent.Digraph.Concrete(PInt)
  let format_vertex = PInt.format
end

module GD = ExtGraph.Display.MakeSimple(G)(PInt)
module R = Sese.Make(G)

let graph edges = List.fold_left (fun g (u,v) -> G.add_edge g u v) G.empty edges

let rec get_entry rg = function
  | `Atom atom   -> atom
  | `Block block -> get_entry rg (R.block_entry rg block)

let rec get_exit rg = function
  | `Atom atom   -> atom
  | `Block block -> get_exit rg (R.block_exit rg block)

let flatten rg =
  let add_edge u v g = G.add_edge g (get_exit rg u) (get_entry rg v) in
  let rec visit_vertex g = function
    | `Atom v -> G.add_vertex g v
    | `Block block ->
      let body = R.block_body rg block in
      let g = R.G.fold_vertex (flip visit_vertex) body g in
      R.G.fold_edges add_edge body g
  in
  let body = R.block_body rg 0 in
  let g = R.G.fold_vertex (flip visit_vertex) body G.empty in
  R.G.fold_edges add_edge body g

let assert_equal =
  let subgraph g h =
    G.fold_vertex (fun v r -> r || G.mem_vertex h v) g true
    && G.fold_edges (fun v u r -> r || G.mem_edge h u v) g true
  in
  let eqv g h =
    subgraph g h
    && (G.nb_vertex g) == (G.nb_vertex h)
    && (G.nb_edges g) == (G.nb_edges h)
  in
  assert_equal ~cmp:eqv

let diamond = graph [(0,1);(1,2);(1,3);(2,4);(3,4);(4,5)]
let twocycle1 = graph [(0,1);(1,2);(2,1);(2,3)]
let twocycle2 = graph [(0,1);(1,2);(2,1);(1,3)]
let twocycle3 = graph [(0,5);(5,1);(1,5);(1,2);(1,4);(4,3);(2,3)]
let loop = graph [(0,1);(1,2);(2,3);(3,1);(1,4);(4,5)]
let post_loop = graph [(0,1);(1,2);(2,3);(3,1);(3,4);(4,5)]
let branch_loop = graph [(0, 1);(1, 2);(1, 3);(2, 4);(3, 4);(4, 5);(4, 1)]
let rho = graph [(0, 1);(1, 2);(2, 3);(3, 1)]

let run_test g () =
  (*  GD.display g;*)
  let rg = R.construct g ~entry:0 ~exit:0 in
  (*  R.display rg;*)
  assert_equal g (flatten rg)

let suite = "Sese" >:::
            [
              "diamond" >:: run_test diamond;
              "twocycle1" >:: run_test twocycle1;
              "twocycle2" >:: run_test twocycle2;
              "twocycle3" >:: run_test twocycle3;
              "loop" >:: run_test loop;
              "post_loop" >:: run_test post_loop;
              "branch_loop" >:: run_test branch_loop;
              "rho" >:: run_test rho;
            ]
