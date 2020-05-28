open Srk
open OUnit

module G = Graph.Persistent.Digraph.ConcreteBidirectional(SrkUtil.Int)

type path_len =
  | Finite of int
  | Infinity
[@@deriving eq,show]
  
module MaxPath = struct
  type t = path_len [@@deriving eq]

  type edge = G.E.t

  let join x y = match x,y with
    | Finite x, Finite y -> Finite (max x y)
    | _, _ -> Infinity

  let widening x y =
    match x,y with
    | Finite x, Finite y when x = y -> Finite x
    | _, _ -> Infinity

  let transform _ = function
    | Infinity -> Infinity
    | Finite x -> Finite (x + 1)
end
module MaxPathAnalysis = Fixpoint.Make(G)(MaxPath)

let mk_graph edges =
  List.fold_left
    (fun g (u,v) -> G.add_edge g u v)
    G.empty
    edges

let suite = "Fixpoint" >::: [
      "diamond" >:: (fun () ->
        let g = mk_graph [(0, 1); (0, 2); (2,3); (3,4); (1,4)] in
        let path_len = MaxPathAnalysis.analyze g (fun _ -> Finite 0) in
        assert_equal (Finite 0) (path_len 0);
        assert_equal (Finite 1) (path_len 1);
        assert_equal (Finite 1) (path_len 2);
        assert_equal (Finite 2) (path_len 3);
        assert_equal (Finite 3) (path_len 4);
      );

      "check" >:: (fun () ->
        let g = mk_graph [(0, 1); (2, 1); (3,2)] in
        let path_len = MaxPathAnalysis.analyze g (fun _ -> Finite 0) in
        assert_equal (Finite 2) (path_len 1);
      );

      "loop" >:: (fun () ->
        let g = mk_graph [(0, 1); (1, 1); (1,2)] in
        let path_len = MaxPathAnalysis.analyze g (fun _ -> Finite 0) in
        assert_equal (Finite 0) (path_len 0);
        assert_equal Infinity (path_len 1);
        assert_equal Infinity (path_len 2);
      );

      "irreducible" >:: (fun () ->
        let g = mk_graph [(0, 1); (1, 0); (1,1); (0,0)] in
        let path_len = MaxPathAnalysis.analyze g (fun _ -> Finite 0) in
        assert_equal Infinity (path_len 0);
        assert_equal Infinity (path_len 1);
      );

  ]
