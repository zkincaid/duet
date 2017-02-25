open OUnit
open Graph
open RecGraph

module ZMin = struct
  include Ka.ZMin
  type var = unit
  let exists _ k = k
  let widen = add
end
open ZMin

module V = struct
  module M = struct
    type t =
      | A of int
      | B of string
            [@@deriving show,ord]
    let equal = (=)
    let hash = Hashtbl.hash
  end
  include M
  module HT = BatHashtbl.Make(M)
  module Map = Putil.Map.Make(M)
  module Set = Putil.Hashed.Set.Make(M)
  type atom = int
  type block = string
  type ('a,'b) typ = ('a,'b) RecGraph.seq_typ

  let classify x  = match x with
    | A x -> `Atom x
    | B x -> `Block x
end
open V

module R = RecGraph.Make(V)(Putil.PString)
module D = Pathexp.MakeSeqRG(R)(Putil.PString)(ZMin)

let rec make = function
  | [] -> R.empty
  | (name, en, ex, edges)::rest ->
    let f g (x, y) = R.G.add_edge g x y in
    let body = List.fold_left f R.G.empty edges in
    let rg = make rest in
    R.add_block rg name body ~entry:en ~exit:ex

let g0 =
  make [
    ("main", A 0, A 2,
     [(A 0, B "bar"); (A 0, A 1);
      (A 1, B "foo");
      (B "foo", A 2);
      (B "bar", A 2); (B "bar", B "baz");
      (B "baz", A 2)]);

    ("foo", A 0, A 2,
     [(A 0, A 1); (A 1, A 2)]);

    ("bar", A 0, A 1,
     [(A 0, A 1)]);

    ("baz", A 0, A 2,
     [(A 0, A 1); (A 1, A 2)])
  ]

let test_g0 () =
  let query = D.mk_query g0 (fun _ -> Z 1) (fun _ _ -> true) "main" in
  let summary = D.get_summary query in
  let assert_summary (dst,d) =
    ("Distance summary for block " ^ dst)
    >:: (fun () ->
        assert_equal ~printer:Ka.ZMin.show d (summary dst))
  in
  let distance = lazy (D.single_src_blocks query) in
  let assert_distance (dst,d) =
    ("Distance to block " ^ dst)
    >:: (fun () ->
        assert_equal ~printer:Ka.ZMin.show d ((Lazy.force distance) dst))
  in
  "G0" >:::
  ((List.map assert_summary
      [("foo", Z 2);
       ("bar", Z 1);
       ("baz", Z 2);])
   @ (List.map assert_distance
        [("foo", Z 2);
         ("bar", Z 1);
         ("baz", Z 2)]))

let g1 =
  make [
    ("main", A 0, B "bar",
     [(A 0, B "foo");
      (A 0, A 1);
      (A 1, A 2);
      (A 2, A 3);
      (A 3, B "bar")]);

    ("foo", A 0, A 2,
     [(A 0, B "baz");
      (B "baz", A 2)]);

    ("bar", A 0, A 1,
     [(A 0, A 1)]);

    ("baz", A 0, A 1,
     [(A 0, B "bar");
      (B "bar", A 1)])
  ]

let test_g1 () =
  let query = D.mk_query g1 (fun _ -> Z 1) (fun _ _ -> true) "main" in
  let summary = D.get_summary query in
  let assert_summary (dst,d) =
    ("Distance summary for block " ^ dst)
    >:: (fun () -> assert_equal ~printer:Ka.ZMin.show d (summary dst))
  in
  let distance = lazy (D.single_src_blocks query) in
  let assert_distance (dst,d) =
    ("Distance to block " ^ dst)
    >:: (fun () ->
        assert_equal ~printer:Ka.ZMin.show d ((Lazy.force distance) dst))
  in
  "G1" >:::
  ((List.map assert_summary
      [("foo", Z 3);
       ("bar", Z 1);
       ("baz", Z 2);])
   @ (List.map assert_distance
        [("foo", Z 1);
         ("bar", Z 3);
         ("baz", Z 2)]))

let g2 =
  make [
    ("main", A 0, B "bar",
     [(A 0, B "foo"); (A 0, B "baz");
      (B "baz", B "bar")]);

    ("foo", A 0, A 2,
     [(A 0, B "foo"); (A 0, A 1);
      (A 1, A 2);
      (B "foo", B "bar");
      (B "bar", A 2)]);

    ("bar", A 0, A 1,
     [(A 0, B "foo");
      (B "foo", A 1)]);

    (* No base case! *)
    ("baz", A 0, A 1,
     [(A 0, B "baz");
      (B "baz", A 1)])
  ]

let test_g2 () =
  let query = D.mk_query g2 (fun _ -> Z 1) (fun _ _ -> true) "main" in
  let summary = D.get_summary query in
  let assert_summary (dst,d) =
    ("Distance summary for block " ^ dst)
    >:: (fun () -> assert_equal ~printer:Ka.ZMin.show d (summary dst))
  in
  let distance = lazy (D.single_src_blocks query) in
  let assert_distance (dst,d) =
    ("Distance to block " ^ dst)
    >:: (fun () ->
        assert_equal ~printer:Ka.ZMin.show d (Lazy.force (distance) dst))
  in
  "G2" >:::
  ((List.map assert_summary
      [("foo", Z 2);
       ("bar", Z 3);
       ("baz", PosInfinity);])
   @ (List.map assert_distance
        [("foo", Z 1);
         ("bar", Z 4);
         ("baz", Z 1)]))

let suite = "RecGraph" >:::
            [
              test_g0 ();
              test_g1 ();
              test_g2 ();
            ]
