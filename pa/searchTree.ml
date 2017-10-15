open Pervasives
open BatPervasives
open Ark

include Log.Make(struct let name = "SearchTree" end)

module type Element = sig
  type t
  val compare : t -> t -> int
  val hash : t -> int
  val equal : t -> t -> bool
  val pp : Format.formatter -> t -> unit
end

module type S = sig
  type t
  type baseSet
  type elt

  val empty : baseSet -> (elt -> baseSet) -> t
  val make  : baseSet -> (elt -> baseSet) -> elt BatSet.t -> t

  exception Item_not_known
  val insert : t -> elt -> unit
  val covered : (elt -> elt -> bool) -> t -> elt -> elt option
end

(* Elt is the type of elements stored in the tree

   Where sets of Base elements label the nodes of
   the tree.

   The function project, takes elements to be inserted
   / searched and gets the corresponding set of Base
   elements.

   The search function performs a range search
   (similar to a K-D tree).
 *)
module Make (Base : Element) (Elt : Element) = struct
  module BaseSet = BatSet.Make(Base)

  type baseSet = BaseSet.t
  type elt = Elt.t

  type tree = (* Every node is a set of elements *)
    Leaf
  | Node of node
  and node =
    { mutable data : elt list;
      left : tree;
      right : tree }

  type t =
    { project : elt -> baseSet;
      elements : baseSet;
      mutable tree : tree }

  let empty elts proj = { project = proj; elements = elts; tree = Leaf }

  let pp_base formatter b =
    Format.fprintf formatter "{%a}"
    (ArkUtil.pp_print_enum Base.pp) (BaseSet.enum b)

  (* This Inserts an ElementSet into the tree
     The path prefix is decided based on subset ordering
     of the element's projection.
  *)
  exception Item_not_known
  let insert stree item =
    let iblist = BaseSet.elements (stree.project item) in (* project item to base set *)
    let elist = BaseSet.elements stree.elements in
    let rec go elist iblist tree =
      match iblist with
        [] ->
        begin
          match tree with
            Leaf -> Node {data = ([item]); left = Leaf; right = Leaf}
          | Node {data; left; right} -> Node {data=(item :: data); left; right}
        end
      | i :: iblist' ->
        match elist with
          [] -> Log.logf ~level:`always "insert: %a" Base.pp i; raise Item_not_known
        | e :: elist ->
          match tree with
            Leaf ->
              if Base.equal i e then
                Node {data = []; left = Leaf; right = (go elist iblist' Leaf)}
              else
                Node {data = []; left = (go elist iblist Leaf); right = Leaf}
          | Node {data; left; right} ->
              if Base.equal i e then
                Node {data; left; right = (go elist iblist' right)}
              else
                Node {data; left = (go elist iblist left); right}
      in stree.tree <- go elist iblist stree.tree

  (* Makes a Search Tree by creating an empty tree and
     inserting each item into the tree *)
  let make elts proj items =
    let tree = empty elts proj in
    let f item =
      insert tree item
    in
    BatSet.iter f items;
    tree

  (* This performs the actual search
     returns true if there exists a elt in tree
     such that (p elt item)

     This only works if (p elt item) =>
     (project elt) is a subset of (project item)
  *)
  let covered p stree item =
    let iblist = BaseSet.elements (stree.project item) in
    let elist = BaseSet.elements stree.elements in
    let f data =
      let g opt d =
        match opt with
          None -> if (p d item) then Some d else None
        | Some _ -> opt
      in
      List.fold_left g None data
    in
    let rec go elist iblist tree =
      match tree with
        Leaf -> None
      | Node {data; left; right} ->
        match f data with
          Some x -> Some x
        | None ->
           match iblist, elist with
           | i :: iblist', e :: elist ->
              begin
                if i = e then
                  match go elist iblist' right with
                  | None -> go elist iblist' left
                  | sx -> sx
                else
                  go elist iblist left
              end
           | [], _ -> None
           | _, [] -> raise Item_not_known
    in go elist iblist stree.tree

end
