open Srk
open OUnit
open Syntax
open Test_pervasives
open BatPervasives

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
  let compare = Stdlib.compare
  let symbol_of = Hashtbl.find sym_table
  let of_symbol sym =
    if Hashtbl.mem rev_sym_table sym then
      Some (Hashtbl.find rev_sym_table sym)
    else
      None
  let is_global _ = true
  let equal = (=)
  let hash = Hashtbl.hash
end
module T = Transition.Make(Ctx)(V)
module WG = WeightedGraph
module TS = TransitionSystem.Make(Ctx)(V)(T)

let () =
  T.domain := (module Iteration.Split(val !T.domain))

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

let mk_ts edges call_edges =
  let rg =
    List.fold_left (fun rg (src, _, tgt) ->
        WG.add_vertex (WG.add_vertex rg src) tgt)
      TS.empty
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
        WG.add_edge rg src (TransitionSystem.Weight w) tgt)
      rg
      edges
  in
  let rg =
    List.fold_left (fun rg (src, (s,t), tgt) ->
        WG.add_edge rg src (TransitionSystem.Call (s,t)) tgt)
      rg
      call_edges
  in
  rg

module TransitionDom = struct
  type weight = T.t
  type abstract_weight = T.t
  let concretize x = x
  let abstract x = x
  let equal = T.equal
  let widen = T.widen
end

let mk_query edges call_edges src =
  TS.mk_query (mk_ts edges call_edges) src (module TransitionDom)
    
let pe_context = Pathexpr.mk_context ()

let pe_algebra =
  let open Pathexpr in
  WG.{ mul = mk_mul pe_context;
       add = mk_add pe_context;
       star = mk_star pe_context;
       zero = mk_zero pe_context;
       one = mk_one pe_context }

let mk_pathgraph =
  let open Pathexpr in
  List.fold_left (fun wg (u,v) ->
      WG.add_edge wg u (mk_edge pe_context u v) v)
    (WG.empty pe_algebra)

let pathexpr_naive wg src tgt =
  let start = WG.max_vertex wg + 1 in
  let final = start + 1 in
  let wg' = WG.add_vertex (WG.add_vertex wg start) final in
  let wg' =
    WG.add_edge
      (WG.add_edge wg' tgt pe_algebra.one final)
      start
      pe_algebra.one
      src
  in
  let result = WG.fold_vertex (fun v wg -> WG.contract_vertex wg v) wg wg' in
  WG.edge_weight result start final

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
      0
  in
  let path = TS.path_weight query 3 in
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
      0
  in
  let path = TS.path_weight query 2 in
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
      0
  in
  let path = TS.path_weight query 8 in
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
      0
  in
  assert_post (TS.path_weight query 3) (x = (int 10));
  assert_post (TS.path_weight query 1) (x <= (int 10));
  assert_not_post (TS.call_weight query (10, 11)) (x <= (int 10));
  assert_not_post (TS.path_weight query 1) ((int 0) <= x)

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
      0
  in
  assert_post (TS.path_weight query 2) (x + y = (int 100));
  assert_not_post (TS.path_weight query 2) (y <= (int 99))

module D = Abstract.MakeAbstractRSY(Ctx)

let affine_invariants =
  TS.forward_invariants (module TS.LiftIncr(D.AffineRelation))

let aff_eq1 () =
  let open Infix in
  let ts =
    mk_ts
      [(0, T.parallel_assign [("x", int 0); ("y", int 10)], 1);
       (1, T.assume (x <= (int 10)), 2);
       (2, T.assign "x" (x + (int 1)), 3);
       (3, T.assign "y" (y + (int 1)), 1)]
      []
  in
  let inv = affine_invariants ts 0 in
  assert_equiv_formula (y - x = (int 10)) (SrkApron.formula_of_property (inv 1));
  assert_equiv_formula (y - x = (int 9)) (SrkApron.formula_of_property (inv 3))

let aff_collatz () =
  let open Infix in
  let ts =
    mk_ts
      [
        (0, T.assign "x" y, 1);
       (1,
        T.parallel_assign
          [("x",
            mk_ite srk
              (x mod (int 2) = (int 0))
              (x / (int 2))
              ((int 3) * x + (int 1)));
           ("y",
            mk_ite srk
              (y mod (int 2) = (int 0))
              (y / (int 2))
              ((int 3) * y + (int 1)))],
        1)]
      []
  in
  let inv = affine_invariants ts 0 in
  assert_equiv_formula (x = y) (SrkApron.formula_of_property (inv 1))

let aff_karr_fig4 () =
  let open Infix in
  let ts =
    mk_ts
      [
        (0, T.assign "x" (y + (int 1)), 1);
        (0, T.assign "y" (x + (int 1)), 2);
        (1, T.assign "x" (x - (int 2)), 2);
        (2, T.assign "y" (y - (int 2)), 1);
      ]
      []
  in
  let inv = affine_invariants ts 0 in
  assert_equiv_formula (x = y + (int 1)) (SrkApron.formula_of_property (inv 1));
  assert_equiv_formula (x = y - (int 1)) (SrkApron.formula_of_property (inv 2))

let aff_karr_fig5 () =
  let open Infix in
  let ts =
    mk_ts
      [(0,
        T.parallel_assign
          [("x", int 2);
           ("y", z + (int 5))],
        1);
       (1,
        T.parallel_assign
          [("x", x + int 1);
           ("y", y + (int 3))],
        1)]
      []
  in
  let inv = affine_invariants ts 0 in
  assert_equiv_formula
    ((int 3)*x - y + z = (int 1))
    (SrkApron.formula_of_property (inv 1))

module G = Graph.Persistent.Digraph.ConcreteBidirectional(SrkUtil.Int)
module ISet = struct
  include SrkUtil.Int.Set
  let show =
    SrkUtil.mk_show
      (fun formatter x ->
        Format.fprintf formatter "{@[<hov 1>%a@]}"
          (SrkUtil.pp_print_enum Format.pp_print_int) (enum x))
end

(* Lengths of simple paths *)
let pathlen_algebra = function
  | `Edge (_, _) -> ISet.singleton 1
  | `Add (x, y) -> ISet.union x y
  | `Zero -> ISet.empty
  | `One -> ISet.singleton 0
  | `Star _ -> ISet.singleton 0
  | `Mul (x, y) ->
     SrkUtil.cartesian_product
       (ISet.enum x)
       (ISet.enum y)
     |> BatEnum.map (fun (x,y) -> x + y)
     |> ISet.of_enum
  | `Segment x -> x

let pathlen_omega_algebra = function
  | `Add (x, y) -> ISet.union x y;
  | `Mul (_, y) -> y
  | `Omega x -> x

let omega_pathexpr
    : (Pathexpr.simple Pathexpr.t,
       Pathexpr.simple Pathexpr.omega) WG.omega_algebra =
  let open Pathexpr in
  WG.{ omega = mk_omega pe_context;
       omega_add = mk_omega_add pe_context;
       omega_mul = mk_omega_mul pe_context }

module PathlenDomain = struct
  type weight = ISet.t
  type abstract_weight = ISet.t
  let abstract x = x
  let concretize x = x
  let equal = ISet.equal
  let widen = ISet.inter
end

let mk_pathlen_query edges call_edges src =
  let open WG in
  let g =
    List.fold_left
      (fun g (u,v) -> RecGraph.add_edge g u v)
      (RecGraph.empty ())
      edges
  in
  let g =
    List.fold_left
      (fun g (u, (s, t), v) -> RecGraph.add_call_edge g u (s, t) v)
      g
      call_edges
  in
  let query = RecGraph.mk_query g src in
  RecGraph.summarize_iterative query pathlen_algebra (module PathlenDomain)

let get_cyclelen query =
  WG.RecGraph.omega_path_weight query pathlen_omega_algebra

let suite = "WeightedGraph" >::: [
    "simple_loop" >:: simple_loop;
    "simple_branch" >:: simple_branch;
    "nested_loop" >:: nested_loop;
    "nonrec_call" >:: nonrec_call;
    "recursive" >:: recursive;
    "aff_eq1" >:: aff_eq1;
    "aff_collatz" >:: aff_collatz;
    "aff_karr_fig4" >:: aff_karr_fig4;
    "aff_karr_fig5" >:: aff_karr_fig5;

    "msat1" >:: (fun () ->
      let g =
        mk_pathgraph [(0, 0); (0, 1); (1, 2); (2, 3); (3, 2)]
      in
      let cg = WG.msat_path_weight g [0] in
      (0 -- 0)
      |> BatEnum.iter (fun v ->
             assert_equal_pathexpr pe_context
               (pathexpr_naive g 0 v)
               (WG.edge_weight cg 0 v))
    );

    "nested" >:: (fun () ->
      let g =
        mk_pathgraph [(0, 1); (1, 2); (2, 3); (3, 4); (4, 3); (4, 5); (5, 1); (5, 5)]
      in
      let cg = WG.msat_path_weight g [0] in
      (0 -- 5)
      |> BatEnum.iter (fun v ->
             assert_equal_pathexpr pe_context
               (pathexpr_naive g 0 v)
               (WG.edge_weight cg 0 v))
    );

    "irreducible" >:: (fun () ->
      let g =
        mk_pathgraph [(0, 1); (0, 2); (1, 2); (2, 1)]
      in
      let cg = WG.msat_path_weight g [0] in
      (0 -- 2)
      |> BatEnum.iter (fun v ->
             assert_equal_pathexpr pe_context
               (pathexpr_naive g 0 v)
               (WG.edge_weight cg 0 v))
    );

    "dag1" >:: (fun () ->
      let g =
        mk_pathgraph [(0, 1); (1, 2); (2, 3); (1, 3)]
      in
      let cg = WG.msat_path_weight g [0] in
      (0 -- 3)
      |> BatEnum.iter (fun v ->
             assert_equal_pathexpr pe_context
               (pathexpr_naive g 0 v)
               (WG.edge_weight cg 0 v))
    );

    "dag2" >:: (fun () ->
      let g =
        mk_pathgraph [(0, 1); (1, 2); (1, 3); (3, 4); (4, 5); (0, 5); (2, 4)]
      in
      let cg = WG.msat_path_weight g [0] in
      (0 -- 5)
      |> BatEnum.iter (fun v ->
             assert_equal_pathexpr pe_context
               (pathexpr_naive g 0 v)
               (WG.edge_weight cg 0 v))
    );

    "branch_loop" >:: (fun () ->
      let g =
        mk_pathgraph [(0, 1); (1, 2); (1, 3); (3, 1); (2, 4); (4, 1)]
      in
      let cg = WG.msat_path_weight g [0] in
      (0 -- 4)
      |> BatEnum.iter (fun v ->
             assert_equal_pathexpr pe_context
               (pathexpr_naive g 0 v)
               (WG.edge_weight cg 0 v))
    );

    "unreachable" >:: (fun () ->
      let g =
        mk_pathgraph [(0, 1); (1, 0); (2, 3); (3, 1); (4, 4)]
      in
      let cg = WG.msat_path_weight g [0; 1; 2; 3; 4] in
      (0 -- 4)
      |> BatEnum.iter (fun u ->
             (0 -- 4) |> BatEnum.iter (fun v ->
                             assert_equal_pathexpr pe_context
                               (pathexpr_naive g u v)
                               (WG.edge_weight cg u v)))
    );

    "msat2" >:: (fun () ->
      let g =
        mk_pathgraph [(0, 2); (1, 2); (2, 3); (1, 4); (4, 2); (2, 0); (3, 1)]
      in
      let cg = WG.msat_path_weight g [0; 1; 2] in
      (0 -- 2)
      |> BatEnum.iter (fun u ->
             (0 -- 4) |> BatEnum.iter (fun v ->
                             assert_equal_pathexpr pe_context
                               (pathexpr_naive g u v)
                               (WG.edge_weight cg u v))
           )
    );

    "deep_call" >:: (fun () ->
      let open Infix in
      let query =
        mk_query
          [(0, T.assign "x" (int 0), 1);
           (3, T.assign "x" (x + (int 1)), 4);
           (6, T.assign "x" (x + (int 2)), 7);
           (9, T.assign "x" (x + (int 3)), 10)]
          [(1, (3, 5), 2);
           (4, (6, 8), 5);
           (7, (9, 10), 8)]
          0
      in
      assert_post (TS.path_weight query 7) (x = (int 3));
      assert_not_post (TS.path_weight query 7) fls;
      assert_post (TS.path_weight query 10) (x = (int 6));
      assert_not_post (TS.path_weight query 10) fls);

    "branching_cycle" >:: (fun () ->
      let query = mk_pathlen_query
                    [(0, 1); (1, 2); (2, 3); (3, 1); (2, 1)]
                    []
                    0
      in
      assert_equal ~cmp:ISet.equal ~printer:ISet.show
        (ISet.of_list [2; 3])
        (get_cyclelen query));

    "nested_cycle" >:: (fun () ->
      let query = mk_pathlen_query
                    [(0, 1); (1, 2); (2, 3); (3, 2); (3, 4); (4, 1); (4, 4)]
                    []
                    0
      in
      assert_equal ~cmp:ISet.equal ~printer:ISet.show
        (ISet.of_list [1; 2; 4])
        (get_cyclelen query));

    "branch_loops" >:: (fun () ->
      let query = mk_pathlen_query
                    [(0, 1); (0, 2); (2, 3); (3, 2); (1, 1);
                     (4, 5); (5, 6); (6, 4)]
                    []
                    0
      in
      assert_equal ~cmp:ISet.equal ~printer:ISet.show
        (ISet.of_list [1; 2])
        (get_cyclelen query));

    "recursive_cycle" >:: (fun () ->
      let query = mk_pathlen_query
                    [(0, 1); (1, 2); (2, 3); (3, 4)]
                    [(2, (0, 4), 4)]
                    0
      in
      assert_equal ~cmp:ISet.equal ~printer:ISet.show
        (ISet.of_list [2])
        (get_cyclelen query));

    "mutual_recursive_cycle" >:: (fun () ->
      let query = mk_pathlen_query
                    [(0, 1); (1, 2); (2, 3);
                     (4, 5); (5, 6); (6, 7) ]
                    [(1, (4, 6), 3);
                     (5, (0, 3), 7)]
                    0
      in
      assert_equal ~cmp:ISet.equal ~printer:ISet.show
        (ISet.of_list [2])
        (get_cyclelen query))
  ]
