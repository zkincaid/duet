(*pp camlp4find deriving.syntax *)
open OUnit
open Graph
open Regex

module R = struct
  include Regex.NormalizedRegex(struct
				  type t = char deriving (Show,Compare)
				  let format = Show_t.format
				  let show = Show_t.show
				  let compare = Pervasives.compare
				  let consistent = (=)
				end)
end

module V = struct
  type t = int deriving (Compare)
  let equal = (=)
  let compare = Pervasives.compare
  let hash x = x
end
module E = struct
  type t = Putil.PChar.t option deriving (Compare, Show)
  let compare = Compare_t.compare
  let default = None
end
module G = struct
  include Persistent.Digraph.ConcreteLabeled(V)(E)
end
module Oper = Oper.P(G)
open R

let g =
  let vertices = [0;1;2;3;4;5] in
  let edges =
    [(0, 'a', 1);
     (1, 'b', 2);
     (1, 'c', 3);
     (2, 'a', 4);
     (3, 'b', 4);
     (4, 'd', 5);
     (4, 'a', 1)]
  in
  let add_edge g (src, label, target) =
    G.add_edge_e g (G.E.create src (Some label) target)
  in
    List.fold_left
      add_edge
      (List.fold_left G.add_vertex G.empty vertices)
      edges

type fa = { start: int;
	    final: int list;
	    graph: G.t }

let automaton k =
  let max_state = ref 0 in
  let new_state () =
    let s = !max_state in
    max_state := !max_state + 1;
    s
  in
  let f = function
    | OEmpty ->
      let v = new_state () in
      { start = v;
	final = [];
	graph = G.add_vertex G.empty v }
    | OEpsilon ->
      let v = new_state () in
      { start = v;
	final = [v];
	graph = G.add_vertex G.empty v }
    | OCat (a, b) ->
      let graph =
	List.fold_left
	  (fun g x -> G.add_edge_e g (G.E.create x None b.start))
	  (Oper.union a.graph b.graph)
	  a.final
      in
      { start = a.start;
	final = b.final;
	graph = graph }
    | OAlpha x ->
      let u = new_state () in
      let v = new_state () in
      let graph =
	G.add_edge_e
	  (G.add_vertex (G.add_vertex G.empty v) u)
	  (G.E.create u (Some x) v)
      in
      { start = u;
	final = [v];
	graph = graph }
    | OUnion (a, b) ->
      let v = new_state () in
      let final = new_state () in
      let graph =
	G.add_edge_e
	  (G.add_edge_e
	     (G.add_vertex (Oper.union a.graph b.graph) v)
	     (G.E.create v None a.start))
	  (G.E.create v None b.start)
      in
      let graph =
	List.fold_left
	  (fun g v -> G.add_edge_e g (G.E.create v None final))
	  graph
	  (a.final @ b.final)
      in
      { start = v;
	final = [final];
	graph = graph }
    | OStar a ->
      let v = new_state () in
      let graph =
	List.fold_left
	  (fun g f -> G.add_edge_e g (G.E.create f None v))
	  (G.add_edge_e a.graph (G.E.create v None a.start))
	  a.final
      in
      { start = v;
	final = [v];
	graph = graph }
  in
  fold_regex f k

open Ka.ZMin
let test_distance name solve =
  let weight e = match G.E.label e with
    | Some 'a' -> Z 1
    | Some 'b' -> Z 2
    | Some 'c' -> Z 3
    | Some 'd' -> Z 4
    | _   -> failwith "Not an edge label"
  in
  let distance = solve g weight in
  let assert_distance (s,e,d) =
    ("Distance " ^ (string_of_int s) ^ " -> " ^ (string_of_int e))
    >:: (fun () -> assert_equal ~printer:Ka.ZMin.show d (distance s e))
  in
    name >:::
      (List.map assert_distance
	 [ (0, 0, Z 0);
	   (0, 1, Z 1);
	   (0, 2, Z 3);
	   (0, 3, Z 4);
	   (0, 4, Z 4);
	   (0, 5, Z 8);

	   (2, 0, PosInfinity);
	   (2, 1, Z 2);
	   (2, 2, Z 0);
	   (2, 3, Z 5);
	   (2, 4, Z 1);
	   (2, 5, Z 5);

	   (5, 4, PosInfinity);
	   (5, 2, PosInfinity);
	   (3, 2, Z 5) ])


let parse_norm x = R.normalize (Test_regex.must_parse x)

module KDist = Pathexp.Make(G)(Ka.ZMin)
module KRegex = Pathexp.Make(G)(R)
module KRegexElim = Pathexp.MakeElim(G)(R)
module KDistElim = Pathexp.MakeElim(G)(Ka.ZMin)

let g_weight e = match G.E.label e with
  | Some c -> alpha c
  | None -> R.one
    
let kleene_regex x =
  let a = automaton (Test_regex.must_parse x) in
  let path = KRegex.all_paths a.graph g_weight in
    List.fold_left (fun r f -> R.add r (path a.start f)) R.zero a.final

let test_regex solve () =
  let g_path = solve g g_weight in
  let assert_equal = assert_equal ~cmp:R.eqv ~printer:R.show in
    assert_equal (parse_norm "a(baa+cba)*(ba+cb)d") (g_path 0 5);
    assert_equal (parse_norm "(baa+cba)*") (g_path 1 1);
    assert_equal (parse_norm "a(a(ba+cb))*a") (g_path 2 1);
    assert_equal R.zero (g_path 1 0);
    assert_equal R.zero (g_path 5 2);
    List.iter (fun x -> assert_equal (parse_norm x) (kleene_regex x))
      ["abc"; "a+b+c"; "a*"; "((a+b)*c)*"; "(a*+(b*c+c*b))*d"]

let test_initial () =
  let parse = parse_norm in
  let weight edge = match G.E.label edge with
    | Some c -> Regex.Alpha c
    | None -> Regex.Epsilon
  in
  let assert_pathexp x =
    let regex = parse x in
    let a = automaton (Test_regex.must_parse x) in
    let final = match a.final with
      | [f] -> f
      | _ -> assert false
    in
    let pathexp = KRegexElim.path_expr a.graph g_weight a.start final in
    assert_equal ~cmp:R.equal ~printer:R.show regex pathexp
  in
  assert_pathexp "abc";
  assert_pathexp "a(b+c)e";
  assert_pathexp "a(bc)*d";
  assert_pathexp "a(b+c)*d";
  assert_pathexp "a((b+c)*+(c+b)*)*d"

let suite = "Pathexp" >:::
  [
    test_distance "Distance" KDist.all_paths;
    test_distance "Elim distance" KDistElim.path_expr;
    test_distance "Elim distance single_src" KDistElim.single_src;
    "Regex" >:: (test_regex KRegex.all_paths);
    "Elim regex" >:: (test_regex KRegexElim.path_expr);
    "Elim regex paths_from" >:: (test_regex KRegexElim.single_src);
    "Pathexp initial algebra" >:: test_initial;
  ]
