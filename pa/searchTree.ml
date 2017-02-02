open Pervasives
open BatPervasives
open Apak

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
  val insert : t -> elt -> unit
  val covered : (elt -> elt -> bool) -> t -> elt -> elt option
end

module Make (Base : Element) (Elt : Element) = struct
  module BaseSet = BatSet.Make(Base)
  module EltSet = BatSet.Make(Elt)

  type baseSet = BaseSet.t
  type elt = Elt.t

  type tree = (* Every node is a set of elements *)
    Leaf
  | Node of node
  and node =
    { mutable data : EltSet.t;
      left : tree;
      right : tree }

  type t =
    { project : elt -> baseSet;
      elements : baseSet;
      mutable tree : tree }

  let empty elts proj = { project = proj; elements = elts; tree = Leaf }

  (* This Inserts an ElementSet into the tree
     The path prefix is decided based on subset ordering *)
  let pp_base formatter b =
    Format.fprintf formatter "{%a}"
    (ApakEnum.pp_print_enum Base.pp) (BaseSet.enum b)

  exception Item_not_known
  let insert stree item =
    let iblist = BaseSet.elements (stree.project item) in (* project item to base set *)
    let elist = BaseSet.elements stree.elements in
    let rec go elist iblist tree =
      match iblist with
        [] ->
        begin
          match tree with
            Leaf -> Node {data = (EltSet.add item EltSet.empty); left = Leaf; right = Leaf}
          | Node {data; left; right} -> Node {data=(EltSet.add item data); left; right}
        end
      | i :: iblist' ->
        match elist with
          [] -> raise Item_not_known
        | e :: elist ->
          match tree with
            Leaf ->
              if Base.equal i e then
                Node {data = EltSet.empty; left = Leaf; right = (go elist iblist' Leaf)}
              else
                Node {data = EltSet.empty; left = (go elist iblist Leaf); right = Leaf}
          | Node {data; left; right} ->
              if Base.equal i e then
                Node {data; left; right = (go elist iblist' right)}
              else
                Node {data; left = (go elist iblist left); right}
      in stree.tree <- go elist iblist stree.tree

  let make elts proj items =
    let tree = empty proj elts in
    let f item =
      insert tree item
    in
    BatSet.iter f items;
    tree

  (* This performs the actual search
     returns true if there exists a elt in tree
     such that (f elt item) *)
  let covered f stree item =
    let neg : int ref = ref 0 in
    let pos : int ref = ref 0 in
    let inc x = x := !x + 1 in
    let iblist = BaseSet.elements (stree.project item) in
    let elist = BaseSet.elements stree.elements in
    let g data =
      let h d opt =
        match opt with
          None -> if (f d item) then begin inc pos; Some d end else begin inc neg; None end
        | Some _ -> opt
      in
      EltSet.fold h data None
    in
    let rec go elist iblist tree =
      match tree with
        Leaf -> None
      | Node {data; left; right} ->
        match g data with
          Some x -> Some x
        | None ->
          begin
            match iblist with
              [] -> None
            | i :: iblist' ->
               match elist with
                 [] -> print_endline "covered"; raise Item_not_known
               | e :: elist ->
                  if i = e then
                    match go elist iblist' left with
                      None -> (go elist iblist' right)
                    | Some x -> Some x
                  else
                    (go elist iblist left)
          end
    in let ret = go elist iblist stree.tree in
       (*       print_int !neg; print_string " "; print_int !pos; print_newline(); *)
       ret
end
