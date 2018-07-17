open OUnit
open Abstract
open Syntax
open SrkApron
open Test_pervasives

module V = struct
  type t = string

  let typ_table = Hashtbl.create 991
  let sym_table = Hashtbl.create 991
  let rev_sym_table = Hashtbl.create 991

  let register_var name typ =
    assert (not (Hashtbl.mem typ_table name));
    let sym = Ctx.mk_symbol ~name (typ :> typ) in
    Hashtbl.add typ_table name typ;
    Hashtbl.add sym_table name sym;
    Hashtbl.add rev_sym_table sym name

  let pp = Format.pp_print_string
  let show x = x
  let typ = Hashtbl.find typ_table
  let compare = Pervasives.compare
  let symbol_of = Hashtbl.find sym_table
  let of_symbol sym =
    if Hashtbl.mem rev_sym_table sym then
      Some (Hashtbl.find rev_sym_table sym)
    else
      None
end
module T = struct
  module SemiRing = Transition.Make(Ctx)(V)
  include SemiRing
  open Iteration
  open SolvablePolynomial
  module I = SemiRing.Iter(MakeDomain(Split(ProductWedge(SolvablePolynomial)(WedgeGuard))))
  let star = I.star
end
module WG = WeightedGraph
module RG = WeightedGraph.MakeRecGraph (struct
    include T
    let project x = x
  end)

let () =
  V.register_var "i" `TyInt;
  V.register_var "j" `TyInt;
  V.register_var "k" `TyInt;
  V.register_var "n" `TyInt;
  V.register_var "x" `TyInt;
  V.register_var "y" `TyInt;
  V.register_var "z" `TyInt

let x = Ctx.mk_const (V.symbol_of "x")
let y = Ctx.mk_const (V.symbol_of "y")
let z = Ctx.mk_const (V.symbol_of "z")
let i = Ctx.mk_const (V.symbol_of "i")
let j = Ctx.mk_const (V.symbol_of "j")
let k = Ctx.mk_const (V.symbol_of "k")
let n = Ctx.mk_const (V.symbol_of "n")

let mk_query edges call_edges =
  let rg =
    List.fold_left (fun rg (src, _, tgt) ->
        WG.add_vertex (WG.add_vertex rg src) tgt)
      RG.empty
      edges
  in
  let rg =
    List.fold_left (fun rg (src, _, tgt) ->
        WG.add_vertex (WG.add_vertex rg src) tgt)
      rg
      call_edges
  in
  let rg = 
    List.fold_left (fun rg (src, w, tgt) ->
        WG.add_edge rg src (WeightedGraph.Weight w) tgt)
      rg
      edges
  in
  let rg =
    List.fold_left (fun rg (src, (s,t), tgt) ->
        WG.add_edge rg src (WeightedGraph.Call (s,t)) tgt)
      rg
      call_edges
  in
  RG.mk_query rg
    
let assert_post tr phi =
  let not_post =
    rewrite srk ~down:(nnf_rewriter srk) (Ctx.mk_not phi)
  in
  let pathcond =
    T.guard (T.mul tr (T.assume not_post))
  in
  if Wedge.is_sat srk pathcond != `Unsat then
    assert_failure (Printf.sprintf "%s\n is not a post-condition of\n%s"
                      (Formula.show srk phi)
                      (T.show tr))

let assert_not_post tr phi =
  let not_post =
    rewrite srk ~down:(nnf_rewriter srk) (Ctx.mk_not phi)
  in
  let pathcond =
    T.guard (T.mul tr (T.assume not_post))
  in
  if Smt.is_sat srk pathcond != `Sat then
    assert_failure (Printf.sprintf "%s\n is a post-condition of\n%s"
                      (Formula.show srk phi)
                      (T.show tr))

let simple_loop () =
  let query =
    let open Infix in
    mk_query
      [(0, T.assign "x" (int 0), 1);
       (1, T.assume (x < (int 10)), 2);
       (2, T.assign "x" (x + (int 1)), 1);
       (1, T.assume ((int 10) <= x), 3)]
      []
  in
  let path = RG.path_weight query 0 3 in
  let post =
    let open Infix in
    (x = (int 10))
  in
  assert_post path post

let simple_branch () =
  let open Infix in
  let query =
    mk_query
      [(0, T.assign "x" (int 0), 1);
       (1, T.assign "x" (x + (int 1)), 2);
       (1, T.assign "x" (x - (int 1)), 2)]
      []
  in
  let path = RG.path_weight query 0 2 in
  assert_post path (x <= (int 1));
  assert_post path ((int (-1)) <= x)

let nested_loop () =
  let open Infix in
  let query =
    mk_query
      [(0, T.assign "x" (int 0), 1);
       (1, T.assign "y" (int 0), 2);
       (2, T.assume (x < (int 10)), 3);
       (3, T.assign "z" (int 0), 4);
       (4, T.assume (z < (int 5)), 5);
       (5, T.assign "z" (z + (int 1)), 6);
       (6, T.assign "y" (y + (int 1)), 4);
       (4, T.assume ((int 5) <= z), 7);
       (7, T.assign "x" (x + (int 1)), 2);
       (2, T.assume ((int 10) <= x), 8)]
      []
  in
  let path = RG.path_weight query 0 8 in
  assert_post path (x = (int 10));
  assert_post path (y = (int 50));
  assert_post path (z = (int 5))

let nonrec_call () =
  let open Infix in
  let query =
    mk_query
      [(0, T.assign "x" (int 0), 1);
       (1, T.assume (x < (int 10)), 2);
       (1, T.assume ((int 10) <= x), 3);
       (10, T.assign "x" (x + (int 1)), 11);
       (10, T.assign "x" (x - (int 1)), 11)]
      [(2, (10, 11), 1)]
  in
  assert_post (RG.path_weight query 0 3) (x = (int 10));
  assert_post (RG.path_weight query 0 1) (x <= (int 10));
  assert_not_post (RG.path_weight query 10 11) (x <= (int 10));
  assert_not_post (RG.path_weight query 0 1) ((int 0) <= x)

let recursive () =
  let open Infix in
  let query =
    mk_query
      [(0, T.parallel_assign [("x", int 100); ("y", int 0)], 1);
       (10, T.assume ((int 0) < x), 11);
       (10, T.assume (x <= (int 0)), 12);
       (11, T.assign "x" (x - (int 1)), 13);
       (14, T.assign "y" (y + (int 1)), 12)]
      [(1, (10, 12), 2);
       (13, (10, 12),14)]
  in
  assert_post (RG.path_weight query 0 2) (x + y = (int 100));
  assert_not_post (RG.path_weight query 0 2) (y <= (int 99))

let suite = "WeightedGraph" >::: [
    "simple_loop" >:: simple_loop;
    "simple_branch" >:: simple_branch;
    "nested_loop" >:: nested_loop;
    "nonrec_call" >:: nonrec_call;
    "recursive" >:: recursive;
  ]
