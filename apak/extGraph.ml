module type G = sig
  include Graph.Sig.G
  val vertices : t -> V.t BatEnum.t
  val edges : t -> (V.t * V.t) BatEnum.t
  val edges_e : t -> E.t BatEnum.t
  val enum_succ : t -> V.t -> V.t BatEnum.t
  val enum_succ_e : t -> V.t -> E.t BatEnum.t
  val enum_pred : t -> V.t -> V.t BatEnum.t
  val enum_pred_e : t -> V.t -> E.t BatEnum.t
end

module type P = sig
  include G
  val empty : t
  val add_vertex : t -> vertex -> t
  val remove_vertex : t -> vertex -> t
  val add_edge : t -> vertex -> vertex -> t
  val add_edge_e : t -> edge -> t
  val remove_edge : t -> vertex -> vertex -> t
  val remove_edge_e : t -> edge -> t
  val union : t -> t -> t
  val intersect : t -> t -> t
end

module type I = sig
  include G
  val create : ?size:int -> unit -> t
  val clear : t -> unit
  val copy : t -> t
  val add_vertex : t -> vertex -> unit
  val remove_vertex : t -> vertex -> unit
  val add_edge : t -> vertex -> vertex -> unit
  val add_edge_e : t -> edge -> unit
  val remove_edge : t -> vertex -> vertex -> unit
  val remove_edge_e : t -> edge -> unit
end

module type Vertex = sig
  type t
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
  module HT : BatHashtbl.S with type key = t
  module Map : Putil.Map.S with type key = t
  module Set : Putil.Hashed.Set.S with type elt = t
end

let display_dot output_dot graph =
  Putil.with_temp_filename "graph" ".png"
    (fun output -> Putil.with_temp_file "graph" ".dot"
        (fun tn tc ->
           output_dot tc graph;
           close_out tc;
           let cmd =
             Printf.sprintf "dot %s -Tpng > %s && eog %s" tn output output
           in
           ignore(Sys.command cmd)))


(* The following module is copied (and slightly modified) from
   ocamlgraph/blocks.ml, which isn't part of the standard API. *)

(**************************************************************************)
(*                                                                        *)
(*  Ocamlgraph: a generic graph library for OCaml                         *)
(*  Copyright (C) 2004-2010                                               *)
(*  Sylvain Conchon, Jean-Christophe Filliatre and Julien Signoles        *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)
module Blocks = struct

  module OTProduct(X: Graph.Sig.ORDERED_TYPE)(Y: Graph.Sig.ORDERED_TYPE) =
  struct
    type t = X.t * Y.t
    let compare (x1, y1) (x2, y2) =
      let cv = X.compare x1 x2 in
      if cv != 0 then cv else Y.compare y1 y2
  end

  (** Common signature to an imperative/persistent association table *)
  module type HM = sig
    type 'a return
    type 'a t
    type key
    val create : ?size:int -> unit -> 'a t
    val create_from : 'a t -> 'a t
    val empty : 'a return
    val clear: 'a t -> unit
    val is_empty : 'a t -> bool
    val add : key -> 'a -> 'a t -> 'a t
    val remove : key -> 'a t -> 'a t
    val mem : key -> 'a t -> bool
    val find : key -> 'a t -> 'a
    val find_and_raise : key -> 'a t -> string -> 'a
    (** [find_and_raise k t s] is equivalent to [find k t] but raises
        [Invalid_argument s] when [find k t] raises [Not_found] *)
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val map : (key -> 'a -> key * 'a) -> 'a t -> 'a t
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val copy : 'a t -> 'a t
    val keys : 'a t -> key BatEnum.t
    val values : 'a t -> 'a BatEnum.t
    val enum : 'a t -> (key * 'a) BatEnum.t
  end

  (** [HM] implementation using hashtbl. *)
  module Make_Hashtbl(X: BatHashtbl.S) = struct

    include X

    type 'a return = unit
    let empty = ()
    (* never call and not visible for the user thank's to signature
       constraints *)

    let create_from h = create (length h)
    let create ?(size=97) () = create size

    let is_empty h = (length h = 0)

    let find_and_raise k h s = try find h k with Not_found -> invalid_arg s

    let map f h =
      let h' = create_from h  in
      iter (fun k v -> let k, v = f k v in add h' k v) h;
      h'

    let add k v h = replace h k v; h
    let remove k h = remove h k; h
    let mem k h = mem h k
    let find k h = find h k
  end

  (** [HM] implementation using map *)
  module Make_Map(X: Putil.Map.S) = struct
    include X
    type 'a return = 'a t
    let is_empty m = (m = empty)
    let create ?size () = assert false
    (* never call and not visible for the user thank's to signature
       constraints *)
    let create_from _ = empty
    let copy m = m
    let map f m = fold (fun k v m -> let k, v = f k v in add k v m) m empty
    let find_and_raise k h s = try find k h with Not_found -> invalid_arg s
    let clear _ = assert false
    (* never call and not visible for the user thank's to signature
       constraints *)
  end

  (** Common implementation to all (directed) graph implementations. *)
  module Minimal
      (S: sig
         type t
         type elt
         val empty : t
         val cardinal : t -> int
         val add : elt -> t -> t
       end)
      (HM: HM) =
  struct

    type vertex = HM.key

    let is_directed = true
    let empty = HM.empty
    let create = HM.create
    let is_empty = HM.is_empty
    let copy = HM.copy
    let clear = HM.clear

    let nb_vertex g = HM.fold (fun _ _ -> succ) g 0
    let nb_edges g = HM.fold (fun _ s n -> n + S.cardinal s) g 0
    let out_degree g v =
      S.cardinal
        (try HM.find v g with Not_found ->
          invalid_arg "[apak] out_degree")

    let mem_vertex g v = HM.mem v g

    let unsafe_add_vertex g v = HM.add v S.empty g
    let unsafe_add_edge g v1 v2 = HM.add v1 (S.add v2 (HM.find v1 g)) g

    let add_vertex g v = if HM.mem v g then g else unsafe_add_vertex g v

    let iter_vertex f = HM.iter (fun v _ -> f v)
    let fold_vertex f = HM.fold (fun v _ -> f v)
    let vertices = HM.keys
  end

  (** All the predecessor operations from the iterators on the edges *)
  module Pred
      (S: sig
         module PV: Vertex
         module PE: Graph.Sig.EDGE with type vertex = PV.t
         type t
         val mem_vertex : PV.t -> t -> bool
         val iter_edges : (PV.t -> PV.t -> unit) -> t -> unit
         val fold_edges : (PV.t -> PV.t -> 'a -> 'a) -> t -> 'a -> 'a
         val iter_edges_e : (PE.t -> unit) -> t -> unit
         val fold_edges_e : (PE.t -> 'a -> 'a) -> t -> 'a -> 'a
         val edges : t -> (PV.t * PV.t) BatEnum.t
         val edges_e : t -> PE.t BatEnum.t
       end) =
  struct

    open S

    let iter_pred f g v =
      if not (mem_vertex v g) then invalid_arg "[apak] iter_pred";
      iter_edges (fun v1 v2 -> if PV.equal v v2 then f v1) g

    let fold_pred f g v =
      if not (mem_vertex v g) then invalid_arg "[apak] fold_pred";
      fold_edges (fun v1 v2 a -> if PV.equal v v2 then f v1 a else a) g

    let pred g v = fold_pred (fun v l -> v :: l) g v []

    let in_degree g v =
      if not (mem_vertex v g) then invalid_arg "[apak] in_degree";
      fold_pred (fun v n -> n + 1) g v 0

    let iter_pred_e f g v =
      if not (mem_vertex v g) then invalid_arg "[apak] iter_pred_e";
      iter_edges_e (fun e -> if PV.equal v (PE.dst e) then f e) g

    let fold_pred_e f g v =
      if not (mem_vertex v g) then invalid_arg "[apak] fold_pred_e";
      fold_edges_e (fun e a -> if PV.equal v (PE.dst e) then f e a else a) g

    let pred_e g v = fold_pred_e (fun v l -> v :: l) g v []

    let enum_pred_e g v =
      if not (mem_vertex v g) then invalid_arg "[apak] fold_pred_e";
      BatEnum.filter (fun e -> PV.equal v (PE.dst e)) (edges_e g)

    let enum_pred g v =
      if not (mem_vertex v g) then invalid_arg "[apak] fold_pred";
      BatEnum.filter_map
        (fun (v1, v2) -> if PV.equal v v2 then Some v1 else None)
        (edges g)
  end

  (** Common implementation to all the unlabeled (directed) graphs. *)
  module Unlabeled(V: Vertex)(HM: HM with type key = V.t) = struct

    module S = V.Set

    module E = struct
      type vertex = V.t
      include OTProduct(V)(V)
      let src = fst
      let dst = snd
      type label = unit
      let label _ = ()
      let create v1 () v2 = v1, v2
    end
    type edge = E.t

    let mem_edge g v1 v2 =
      try S.mem v2 (HM.find v1 g)
      with Not_found -> false

    let mem_edge_e g (v1, v2) = mem_edge g v1 v2

    let find_edge g v1 v2 = if mem_edge g v1 v2 then v1, v2 else raise Not_found
    let find_all_edges g v1 v2 = try [ find_edge g v1 v2 ] with Not_found -> []

    let unsafe_remove_edge g v1 v2 = HM.add v1 (S.remove v2 (HM.find v1 g)) g
    let unsafe_remove_edge_e g (v1, v2) = unsafe_remove_edge g v1 v2

    let remove_edge g v1 v2 =
      if not (HM.mem v2 g) then invalid_arg "[apak] remove_edge";
      HM.add
        v1 (S.remove v2 (HM.find_and_raise v1 g "[apak] remove_edge")) g

    let remove_edge_e g (v1, v2) = remove_edge g v1 v2

    let iter_succ f g v =
      S.iter f (HM.find_and_raise v g "[apak] iter_succ")

    let fold_succ f g v =
      S.fold f (HM.find_and_raise v g "[apak] fold_succ")

    let iter_succ_e f g v = iter_succ (fun v2 -> f (v, v2)) g v
    let fold_succ_e f g v = fold_succ (fun v2 -> f (v, v2)) g v

    let succ g v = S.elements (HM.find_and_raise v g "[apak] succ")
    let succ_e g v = fold_succ_e (fun e l -> e :: l) g v []
    let enum_succ g v = S.enum (HM.find_and_raise v g "[apak] enum_succ")
    let enum_succ_e g v = BatEnum.map (fun u -> (v, u)) (enum_succ g v)

    let map_vertex f =
      HM.map (fun v s -> f v, S.fold (fun v s -> S.add (f v) s) s S.empty)

    module I = struct
      type t = S.t HM.t
      module PV = V
      module PE = E
      let iter_edges f = HM.iter (fun v -> S.iter (f v))
      let fold_edges f = HM.fold (fun v -> S.fold (f v))
      let iter_edges_e f = iter_edges (fun v1 v2 -> f (v1, v2))
      let fold_edges_e f = fold_edges (fun v1 v2 a -> f (v1, v2) a)
      let edges_e g =
        let f (v, s) = BatEnum.map (fun w -> (v, w)) (S.enum s) in
        BatEnum.concat (BatEnum.map f (HM.enum g))
      let edges = edges_e
    end
    include I

    include Pred(struct include I let mem_vertex = HM.mem end)

  end

  (** Common implementation to all the labeled (directed) graphs. *)
  module Labeled
      (V: Vertex)
      (E: Graph.Sig.ORDERED_TYPE_DFT)
      (HM: HM with type key = V.t) =
  struct

    module VE = OTProduct(V)(E)
    module S = BatSet.Make(VE)

    module E = struct
      type vertex = V.t
      type label = E.t
      type t = vertex * label * vertex
      let src (v, _, _) = v
      let dst (_, _, v) = v
      let label (_, l, _) = l
      let create v1 l v2 = v1, l, v2
      module C = OTProduct(V)(VE)
      let compare (x1, x2, x3) (y1, y2, y3) =
        C.compare (x1, (x3, x2)) (y1, (y3, y2))
    end
    type edge = E.t

    let mem_edge g v1 v2 =
      try S.exists (fun (v2', _) -> V.equal v2 v2') (HM.find v1 g)
      with Not_found -> false

    let mem_edge_e g (v1, l, v2) =
      try
        let ve = v2, l in
        S.exists (fun ve' -> VE.compare ve ve' = 0) (HM.find v1 g)
      with Not_found ->
        false

    exception Found of edge
    let find_edge g v1 v2 =
      try
        S.iter
          (fun (v2', l) -> if V.equal v2 v2' then raise (Found (v1, l, v2')))
          (HM.find v1 g);
        raise Not_found
      with Found e ->
        e

    let find_all_edges g v1 v2 =
      try
        S.fold
          (fun (v2', l) acc ->
             if V.equal v2 v2' then (v1, l, v2') :: acc else acc)
          (HM.find v1 g)
          []
      with Not_found ->
        []

    let unsafe_remove_edge g v1 v2 =
      HM.add
        v1
        (S.filter (fun (v2', _) -> not (V.equal v2 v2')) (HM.find v1 g))
        g

    let unsafe_remove_edge_e g (v1, l, v2) =
      HM.add v1 (S.remove (v2, l) (HM.find v1 g)) g

    let remove_edge g v1 v2 =
      if not (HM.mem v2 g) then invalid_arg "[apak] remove_edge";
      HM.add
        v1
        (S.filter
           (fun (v2', _) -> not (V.equal v2 v2'))
           (HM.find_and_raise v1 g "[apak] remove_edge"))
        g

    let remove_edge_e g (v1, l, v2) =
      if not (HM.mem v2 g) then invalid_arg "[apak] remove_edge_e";
      HM.add
        v1
        (S.remove (v2, l) (HM.find_and_raise v1 g "[apak] remove_edge_e"))
        g

    let iter_succ f g v =
      S.iter (fun (w, _) -> f w) (HM.find_and_raise v g "[apak] iter_succ")
    let fold_succ f g v =
      S.fold (fun (w, _) -> f w) (HM.find_and_raise v g "[apak] fold_succ")

    let iter_succ_e f g v =
      S.iter
        (fun (w, l) -> f (v, l, w))
        (HM.find_and_raise v g "[apak] iter_succ_e")

    let fold_succ_e f g v =
      S.fold
        (fun (w, l) -> f (v, l, w))
        (HM.find_and_raise v g "[apak] fold_succ_e")

    let succ g v = fold_succ (fun w l -> w :: l) g v []
    let succ_e g v = fold_succ_e (fun e l -> e :: l) g v []
    let enum_succ_e g v =
      let f (w, l) = (v, l, w) in
      BatEnum.map f (S.enum (HM.find_and_raise v g "[apak] enum_succ_e"))
    let enum_succ g v =
      BatEnum.map fst (S.enum (HM.find_and_raise v g "[apak] enum_succ"))

    let map_vertex f =
      HM.map
        (fun v s -> f v, S.fold (fun (v, l) s -> S.add (f v, l) s) s S.empty)

    module I = struct
      type t = S.t HM.t
      module PV = V
      module PE = E
      let iter_edges f = HM.iter (fun v -> S.iter (fun (w, _) -> f v w))
      let fold_edges f = HM.fold (fun v -> S.fold (fun (w, _) -> f v w))
      let iter_edges_e f =
        HM.iter (fun v -> S.iter (fun (w, l) -> f (v, l, w)))
      let fold_edges_e f =
        HM.fold (fun v -> S.fold (fun (w, l) -> f (v, l, w)))
      let edges_e g =
        let f (v, s) = BatEnum.map (fun (w, l) -> (v, l, w)) (S.enum s) in
        BatEnum.concat (BatEnum.map f (HM.enum g))
      let edges g =
        let f (v, s) = BatEnum.map (fun (w, l) -> (v, w)) (S.enum s) in
        BatEnum.concat (BatEnum.map f (HM.enum g))
    end
    include I

    include Pred(struct include I let mem_vertex = HM.mem end)

  end

  module BidirectionalMinimal(S:Set.S)(HM:HM) = struct

    type vertex = HM.key

    let is_directed = true
    let empty = HM.empty
    let create = HM.create
    let clear = HM.clear
    let is_empty = HM.is_empty
    let copy = HM.copy

    let nb_vertex g = HM.fold (fun _ _ -> succ) g 0
    let nb_edges g = HM.fold (fun _ (_,s) n -> n + S.cardinal s) g 0
    let out_degree g v =
      S.cardinal
        (snd (try HM.find v g
              with Not_found -> invalid_arg "[apak] out_degree"))

    let mem_vertex g v = HM.mem v g

    let unsafe_add_vertex g v = HM.add v (S.empty, S.empty) g
    let add_vertex g v = if HM.mem v g then g else unsafe_add_vertex g v

    let iter_vertex f = HM.iter (fun v _ -> f v)
    let fold_vertex f = HM.fold (fun v _ -> f v)
    let vertices = HM.keys
  end

  module BidirectionalUnlabeled(V:Vertex)(HM:HM with type key = V.t) =
  struct

    module S = BatSet.Make(V)

    module E = struct
      type vertex = V.t
      include OTProduct(V)(V)
      let src = fst
      let dst = snd
      type label = unit
      let label _ = ()
      let create v1 () v2 = v1, v2
    end
    type edge = E.t

    let mem_edge g v1 v2 =
      try S.mem v2 (snd (HM.find v1 g))
      with Not_found -> false

    let mem_edge_e g (v1,v2) = mem_edge g v1 v2

    let find_edge g v1 v2 = if mem_edge g v1 v2 then v1, v2 else raise Not_found
    let find_all_edges g v1 v2 = try [ find_edge g v1 v2 ] with Not_found -> []

    let unsafe_remove_edge g v1 v2 =
      let in_set, out_set = HM.find v1 g in
      let g = HM.add v1 (in_set, S.remove v2 out_set) g in
      let in_set, out_set = HM.find v2 g in
      HM.add v2 (S.remove v1 in_set, out_set) g

    let unsafe_remove_edge_e g (v1,v2) = unsafe_remove_edge g v1 v2

    let remove_edge g v1 v2 =
      if not (HM.mem v2 g && HM.mem v1 g) then
        invalid_arg "[apak] remove_edge";
      unsafe_remove_edge g v1 v2

    let remove_edge_e g (v1, v2) = remove_edge g v1 v2

    let iter_succ f g v =
      S.iter f (snd (HM.find_and_raise v g "[apak] iter_succ"))

    let fold_succ f g v =
      S.fold f (snd (HM.find_and_raise v g "[apak] fold_succ"))

    let iter_succ_e f g v = iter_succ (fun v2 -> f (v, v2)) g v
    let fold_succ_e f g v = fold_succ (fun v2 -> f (v, v2)) g v

    let succ g v = S.elements (snd (HM.find_and_raise v g "[apak] succ"))
    let succ_e g v = fold_succ_e (fun e l -> e :: l) g v []

    let enum_succ g v = S.enum (snd (HM.find_and_raise v g "[apak] enum_succ"))
    let enum_succ_e g v = BatEnum.map (fun u -> (v, u)) (enum_succ g v)

    let map_vertex f =
      HM.map
        (fun v (s1,s2) ->
           f v,
           (S.fold (fun v s -> S.add (f v) s) s1 S.empty,
            S.fold (fun v s -> S.add (f v) s) s2 S.empty))

    module I = struct
      (* we keep sets for both incoming and outgoing edges *)
      type t = (S.t (* incoming *) * S.t (* outgoing *)) HM.t
      module PV = V
      module PE = E
      let iter_edges f = HM.iter (fun v (_, outset) -> S.iter (f v) outset)
      let fold_edges f = HM.fold (fun v (_, outset) -> S.fold (f v) outset)
      let iter_edges_e f = iter_edges (fun v1 v2 -> f (v1, v2))
      let fold_edges_e f = fold_edges (fun v1 v2 a -> f (v1, v2) a)
      let edges_e g =
        let f (v, (_, outset)) =
          BatEnum.map (fun w -> (v, w)) (S.enum outset)
        in
        BatEnum.concat (BatEnum.map f (HM.enum g))
      let edges = edges_e
    end
    include I

    let iter_pred f g v =
      S.iter f (fst (HM.find_and_raise v g "[apak] iter_pred"))

    let fold_pred f g v =
      S.fold f (fst (HM.find_and_raise v g "[apak] fold_pred"))

    let pred g v = S.elements (fst (HM.find_and_raise v g "[apak] pred"))

    let in_degree g v =
      S.cardinal
        (fst (try HM.find v g
              with Not_found -> invalid_arg "[apak] in_degree"))

    let iter_pred_e f g v = iter_pred (fun v2 -> f (v2, v)) g v
    let fold_pred_e f g v = fold_pred (fun v2 -> f (v2, v)) g v

    let pred_e g v = fold_pred_e (fun e l -> e :: l) g v []

    let enum_pred_e g v =
      let pred =
        try fst (HM.find v g)
        with Not_found -> invalid_arg "[apak] in_degree"
      in
      BatEnum.map (fun w -> (v, w)) (S.enum pred)

    let enum_pred g v =
      let pred =
        try fst (HM.find v g)
        with Not_found -> invalid_arg "[apak] in_degree"
      in
      S.enum pred
  end

  module BidirectionalLabeled
      (V:Vertex)(E:Graph.Sig.ORDERED_TYPE)(HM:HM with type key = V.t) =
  struct

    module VE = OTProduct(V)(E)
    module S = BatSet.Make(VE)

    module E = struct
      type vertex = V.t
      type label = E.t
      type t = vertex * label * vertex
      let src (v, _, _) = v
      let dst (_, _, v) = v
      let label (_, l, _) = l
      let create v1 l v2 = v1, l, v2
      module C = OTProduct(V)(VE)
      let compare (x1, x2, x3) (y1, y2, y3) =
        C.compare (x1, (x3, x2)) (y1, (y3, y2))
    end
    type edge = E.t

    let mem_edge g v1 v2 =
      try S.exists (fun (v2', _) -> V.equal v2 v2') (snd (HM.find v1 g))
      with Not_found -> false

    let mem_edge_e g (v1, l, v2) =
      try
        let ve = v2, l in
        S.exists (fun ve' -> VE.compare ve ve' = 0) (snd (HM.find v1 g))
      with Not_found ->
        false

    exception Found of edge
    let find_edge g v1 v2 =
      try
        S.iter
          (fun (v2', l) -> if V.equal v2 v2' then raise (Found (v1, l, v2')))
          (snd (HM.find v1 g));
        raise Not_found
      with Found e ->
        e

    let find_all_edges g v1 v2 =
      try
        S.fold
          (fun (v2', l) acc ->
             if V.equal v2 v2' then (v1, l, v2') :: acc else acc)
          (snd (HM.find v1 g))
          []
      with Not_found ->
        []

    let unsafe_remove_edge g v1 v2 =
      let in_set, out_set = HM.find v1 g in
      let del v set = S.filter (fun (v', _) -> not (V.equal v v')) set in
      let g = HM.add v1 (in_set, del v2 out_set) g in
      let in_set, out_set = HM.find v2 g in
      HM.add v2 (del v1 in_set, out_set) g

    let unsafe_remove_edge_e g (v1, l, v2) =
      let in_set, out_set = HM.find v1 g in
      let g = HM.add v1 (in_set, S.remove (v2, l) out_set) g in
      let in_set, out_set = HM.find v2 g in
      HM.add v2 (S.remove (v1, l) in_set, out_set) g

    let remove_edge g v1 v2 =
      let in_set, out_set = HM.find_and_raise v1 g "[apak] remove_edge" in
      let del v set = S.filter (fun (v', _) -> not (V.equal v v')) set in
      let g = HM.add v1 (in_set, del v2 out_set) g in
      let in_set, out_set = HM.find_and_raise v2 g "[apak] remove_edge" in
      HM.add v2 (del v1 in_set, out_set) g

    let remove_edge_e g (v1, l, v2) =
      let in_set, out_set =
        HM.find_and_raise v1 g "[apak] remove_edge_e"
      in
      let g = HM.add v1 (in_set, S.remove (v2, l) out_set) g in
      let in_set, out_set =
        HM.find_and_raise v2 g "[apak] remove_edge_e"
      in
      HM.add v2 (S.remove (v1, l) in_set, out_set) g

    let iter_succ f g v =
      S.iter
        (fun (w, _) -> f w)
        (snd (HM.find_and_raise v g "[apak] iter_succ"))

    let fold_succ f g v =
      S.fold
        (fun (w, _) -> f w)
        (snd (HM.find_and_raise v g "[apak] fold_succ"))

    let iter_succ_e f g v =
      S.iter
        (fun (w, l) -> f (v, l, w))
        (snd (HM.find_and_raise v g "[apak] iter_succ_e"))

    let fold_succ_e f g v =
      S.fold
        (fun (w, l) -> f (v, l, w))
        (snd (HM.find_and_raise v g "[apak] fold_succ_e"))

    let succ g v = fold_succ (fun w l -> w :: l) g v []
    let succ_e g v = fold_succ_e (fun e l -> e :: l) g v []

    let enum_succ_e g v =
      let f (w, l) = (v, l, w) in
      BatEnum.map f (S.enum (snd (HM.find_and_raise v g "[apak] enum_succ_e")))
    let enum_succ g v =
      BatEnum.map fst (S.enum (snd (HM.find_and_raise v g "[apak] enum_succ")))

    let map_vertex f =
      HM.map
        (fun v (s1,s2) ->
           f v,
           (S.fold (fun (v, l) s -> S.add (f v, l) s) s1 S.empty,
            S.fold (fun (v, l) s -> S.add (f v, l) s) s2 S.empty))

    module I = struct
      type t = (S.t * S.t) HM.t
      module PV = V
      module PE = E
      let iter_edges f = HM.iter (fun v (_,outset) ->
          S.iter (fun (w, _) -> f v w) outset)
      let fold_edges f = HM.fold (fun v (_,outset) ->
          S.fold (fun (w, _) -> f v w) outset)
      let iter_edges_e f = HM.iter (fun v (_,outset) ->
          S.iter (fun (w, l) -> f (v, l, w)) outset)
      let fold_edges_e f = HM.fold (fun v (_,outset) ->
          S.fold (fun (w, l) -> f (v, l, w)) outset)
      let edges_e g =
        let f (v, (_, s)) =
          BatEnum.map (fun (w, l) -> (v, l, w)) (S.enum s)
        in
        BatEnum.concat (BatEnum.map f (HM.enum g))
      let edges g =
        let f (v, (_, s)) =
          BatEnum.map (fun (w, l) -> (v, w)) (S.enum s)
        in
        BatEnum.concat (BatEnum.map f (HM.enum g))
    end
    include I

    let iter_pred f g v =
      S.iter
        (fun (w, _) -> f w)
        (fst (HM.find_and_raise v g "[apak] iter_pred"))

    let fold_pred f g v =
      S.fold
        (fun (w, _) -> f w)
        (fst (HM.find_and_raise v g "[apak] fold_pred"))

    let in_degree g v =
      S.cardinal
        (fst (try HM.find v g
              with Not_found -> invalid_arg "[apak] in_degree"))

    let iter_pred_e f g v =
      S.iter
        (fun (w, l) -> f (w, l, v))
        (fst (HM.find_and_raise v g "[apak] iter_pred_e"))

    let fold_pred_e f g v =
      S.fold
        (fun (w, l) -> f (w, l, v))
        (fst (HM.find_and_raise v g "[apak] fold_pred_e"))

    let pred g v = fold_pred (fun w l -> w :: l) g v []
    let pred_e g v = fold_pred_e (fun e l -> e :: l) g v []

    let enum_pred_e g v =
      let pred = fst (HM.find_and_raise v g "[apak] enum_pred_e") in
      BatEnum.map (fun (w, l) -> (v, l, w)) (S.enum pred)

    let enum_pred g v =
      let pred = fst (HM.find_and_raise v g "[apak] enum_pred_e") in
      BatEnum.map fst (S.enum pred)
  end

  module ConcreteV (V : Vertex) = struct
    include V
    type label = t
    let create v = v
    let label v = v
  end

  module Make
      (V : Vertex)
      (HM : HM with type key = V.t) =
  struct
    module V = ConcreteV(V)
    include Unlabeled(V)(HM)
    include Minimal(S)(HM)

    let add_edge g v1 v2 =
      let g = add_vertex g v1 in
      let g = add_vertex g v2 in
      unsafe_add_edge g v1 v2

    let add_edge_e g (v1, v2) = add_edge g v1 v2
  end

  module MakeBidirectional
      (V : Vertex)
      (HM : HM with type key = V.t) =
  struct
    module V = ConcreteV(V)
    include BidirectionalUnlabeled(V)(HM)
    include BidirectionalMinimal(S)(HM)

    let unsafe_add_edge g v1 v2 =
      let in_set, out_set = HM.find v1 g in
      let g = HM.add v1 (in_set,S.add v2 out_set) g in
      let in_set, out_set = HM.find v2 g in
      HM.add v2 (S.add v1 in_set,out_set) g

    let add_edge g v1 v2 =
      let g = add_vertex g v1 in
      let g = add_vertex g v2 in
      unsafe_add_edge g v1 v2

    let add_edge_e g (v1, v2) = add_edge g v1 v2
  end

  module MakeLabeled
      (V : Vertex)
      (HM : HM with type key = V.t)
      (Edge : Graph.Sig.ORDERED_TYPE_DFT) =
  struct
    module V = ConcreteV(V)
    include Labeled(V)(Edge)(HM)
    include Minimal(S)(HM)

    let add_edge_e g (v1, l, v2) =
      let g = add_vertex g v1 in
      let g = add_vertex g v2 in
      unsafe_add_edge g v1 (v2, l)

    let add_edge g v1 v2 = add_edge_e g (v1, Edge.default, v2)
  end

  module MakeBidirectionalLabeled
      (V : Vertex)
      (HM : HM with type key = V.t)
      (Edge : Graph.Sig.ORDERED_TYPE_DFT) =
  struct
    module V = ConcreteV(V)
    include BidirectionalLabeled(V)(Edge)(HM)
    include BidirectionalMinimal(S)(HM)
    let unsafe_add_edge_e g (v1, l, v2) =
      let in_set, out_set = HM.find v1 g in
      let g = HM.add v1 (in_set,S.add (v2,l) out_set) g in
      let in_set, out_set = HM.find v2 g in
      HM.add v2 (S.add (v1,l) in_set,out_set) g

    let unsafe_add_edge g v1 v2 =
      unsafe_add_edge_e g (v1, Edge.default, v2)

    let add_edge_e g (v1, l, v2) =
      let g = add_vertex g v1 in
      let g = add_vertex g v2 in
      unsafe_add_edge_e g (v1, l, v2)

    let add_edge g v1 v2 = add_edge_e g (v1, Edge.default, v2)
  end
end    

module Persistent = struct
  module Op
      (V : Vertex)
      (S : sig
         type t
         val union : t -> t -> t
         val inter : t -> t -> t
       end) =
  struct
    let union =
      let m _ x y = match x, y with
        | Some succ, None | None, Some succ -> Some succ
        | Some xs, Some ys -> Some (S.union xs ys)
        | None, None -> assert false
      in
      V.Map.merge m

    let intersect =
      let m _ x y = match x, y with
        | Some succ, None | None, Some succ -> None
        | Some xs, Some ys -> Some (S.inter xs ys)
        | None, None -> assert false
      in
      V.Map.merge m
  end

  module BiOp
      (V : Vertex)
      (S : sig
         type t
         val union : t -> t -> t
         val inter : t -> t -> t
       end) =
  struct
    let union =
      let m _ x y = match x, y with
        | Some (p, s), None | None, Some (p, s) -> Some (p, s)
        | Some (xp, xs), Some (yp, ys) -> Some (S.union xp yp, S.union xs ys)
        | None, None -> assert false
      in
      V.Map.merge m

    let intersect =
      let m _ x y = match x, y with
        | Some _, None | None, Some _ -> None
        | Some (xp, xs), Some (yp, ys) -> Some (S.inter xp yp, S.inter xs ys)
        | None, None -> assert false
      in
      V.Map.merge m
  end

  module Digraph = struct
    module Make (V : Vertex) =
    struct
      module HM = Blocks.Make_Map(V.Map)
      include Blocks.Make(V)(HM)
      include Op(V)(S)
      let remove_vertex g v =
        if HM.mem v g then
          let g = HM.remove v g in
          let remove v = S.filter (fun v2 -> not (V.equal v v2)) in
          HM.fold (fun k s -> HM.add k (remove v s)) g empty
        else
          g
    end

    module MakeBidirectional (V : Vertex) =
    struct
      module HM = Blocks.Make_Map(V.Map)
      include Blocks.MakeBidirectional(V)(HM)
      include BiOp(V)(S)
      let remove_vertex g v =
        if HM.mem v g then
          let remove v = S.filter (fun v' -> not (V.equal v v')) in
          let g =
            fold_pred
              (fun v' acc ->
                 let in_set, out_set = HM.find v' acc in
                 HM.add v' (in_set, remove v out_set) acc)
              g v g
          in
          let g =
            fold_succ
              (fun v' acc ->
                 let in_set, out_set = HM.find v' acc in
                 HM.add v' (remove v in_set, out_set) acc)
              g v g
          in
          HM.remove v g
        else
          g
    end

    module MakeLabeled
        (V : Vertex)
        (Edge : Graph.Sig.ORDERED_TYPE_DFT) =
    struct
      module HM = Blocks.Make_Map(V.Map)
      include Blocks.MakeLabeled(V)(HM)(Edge)
      include Op(V)(S)
      let remove_vertex g v =
        if HM.mem v g then
          let g = HM.remove v g in
          let remove v = S.filter (fun (v2, _) -> not (V.equal v v2)) in
          HM.fold (fun k s -> HM.add k (remove v s)) g empty
        else
          g
    end

    module MakeBidirectionalLabeled
        (V : Vertex)
        (Edge : Graph.Sig.ORDERED_TYPE_DFT) =
    struct
      module HM = Blocks.Make_Map(V.Map)
      include Blocks.MakeBidirectionalLabeled(V)(HM)(Edge)
      include BiOp(V)(S)
      let remove_vertex (g:t) (v:vertex) =
        if HM.mem v g then
          let remove v = S.filter (fun (v', _) -> not (V.equal v v')) in
          let g =
            fold_pred
              (fun v' acc ->
                 let in_set, out_set = HM.find v' acc in
                 HM.add v' (in_set, remove v out_set) acc)
              g v g
          in
          let g =
            fold_succ
              (fun v' acc ->
                 let in_set, out_set = HM.find v' acc in
                 HM.add v' (remove v in_set, out_set) acc)
              g v g
          in
          HM.remove v g
        else
          g
    end
  end
end

module Imperative = struct
  module Digraph = struct
    module Make (V : Vertex) =
    struct
      module HM = Blocks.Make_Hashtbl(V.HT)
      include Blocks.Make(V)(HM)
      let add_vertex g v = ignore (add_vertex g v)
      let add_edge g v1 v2 = ignore (add_edge g v1 v2)
      let remove_edge g v1 v2 = ignore (remove_edge g v1 v2)
      let remove_edge_e g e = ignore (remove_edge_e g e)
      let add_edge_e g e = ignore (add_edge_e g e)
      let remove_vertex g v =
        if HM.mem v g then begin
          ignore (HM.remove v g);
          HM.iter (fun k s -> ignore (HM.add k (S.remove v s) g)) g
        end
    end

    module MakeBidirectional (V : Vertex) =
    struct
      module HM = Blocks.Make_Hashtbl(V.HT)
      include Blocks.MakeBidirectional(V)(HM)
      let add_vertex g v = ignore (add_vertex g v)

      let add_edge g v1 v2 =
        add_vertex g v1;
        add_vertex g v2;
        ignore (unsafe_add_edge g v1 v2)

      let add_edge_e g (v1, v2) = add_edge g v1 v2

      let remove_edge g v1 v2 = ignore (remove_edge g v1 v2)
      let remove_edge_e g e = ignore (remove_edge_e g e)

      let remove_vertex g v =
        if HM.mem v g then begin
          iter_pred_e (fun e -> remove_edge_e g e) g v;
          iter_succ_e (fun e -> remove_edge_e g e) g v;
          ignore (HM.remove v g)
        end
    end

    module MakeLabeled
        (V : Vertex)
        (E : Graph.Sig.ORDERED_TYPE_DFT) =
    struct
      module HM = Blocks.Make_Hashtbl(V.HT)
      include Blocks.MakeLabeled(V)(HM)(E)
      let add_vertex g v = ignore (add_vertex g v)
      let remove_edge g v1 v2 = ignore (remove_edge g v1 v2)
      let remove_edge_e g e = ignore (remove_edge_e g e)
      let add_edge_e g e = ignore (add_edge_e g e)
      let add_edge g v1 v2 = ignore (add_edge g v1 v2)
      let remove_vertex g v =
        if HM.mem v g then begin
          ignore (HM.remove v g);
          let remove v = S.filter (fun (v2, _) -> not (V.equal v v2)) in
          HM.iter (fun k s -> ignore (HM.add k (remove v s) g)) g
        end
    end

    module MakeBidirectionalLabeled
        (V : Vertex)
        (E : Graph.Sig.ORDERED_TYPE_DFT) =
    struct
      module HM = Blocks.Make_Hashtbl(V.HT)
      include Blocks.MakeBidirectionalLabeled(V)(HM)(E)

      let add_vertex g v = ignore (add_vertex g v)

      let add_edge g v1 v2 =
        add_vertex g v1;
        add_vertex g v2;
        ignore (unsafe_add_edge g v1 v2)

      let add_edge_e g (v1, l, v2) =
        add_vertex g v1;
        add_vertex g v2;
        ignore (unsafe_add_edge_e g (v1, l, v2))

      let remove_edge g v1 v2 = ignore (remove_edge g v1 v2)
      let remove_edge_e g e = ignore (remove_edge_e g e)

      let remove_vertex g v =
        if HM.mem v g then begin
          iter_pred_e (fun e -> remove_edge_e g e) g v;
          iter_succ_e (fun e -> remove_edge_e g e) g v;
          ignore (HM.remove v g)
        end
    end
  end
end


module ForgetDirection(G : Graph.Sig.G) :
  (Graph.Sig.G with type t = G.t
                and type V.t = G.V.t
                and type E.t = G.E.t) =
struct
  type t = G.t
  module V = G.V
  type vertex = V.t
  module E = G.E
  type edge = G.E.t
  let is_directed = false

  let flip e = E.create (E.dst e) (E.label e) (E.src e)

  let is_empty = G.is_empty
  let nb_vertex = G.nb_vertex
  let nb_edges = G.nb_edges

  let out_degree g v = (G.out_degree g v) + (G.in_degree g v)
  let in_degree = out_degree

  let mem_vertex = G.mem_vertex
  let mem_edge g x y = G.mem_edge g x y || G.mem_edge g y x
  let mem_edge_e g e = G.mem_edge_e g e || G.mem_edge_e g (flip e)
  let find_edge g x y =
    try G.find_edge g x y
    with Not_found -> G.find_edge g y x
  let find_all_edges g x y = (G.find_all_edges g x y) @ (G.find_all_edges g y x)

  let cons x xs = (flip x)::xs

  let succ g v = G.fold_pred (fun x xs -> x::xs) g v (G.succ g v)
  let pred = succ

  let succ_e g v = G.fold_pred_e cons g v (G.succ_e g v)
  let pred_e = succ_e

  let iter_vertex = G.iter_vertex
  let fold_vertex = G.fold_vertex
  let iter_edges = G.iter_edges
  let fold_edges = G.fold_edges
  let iter_edges_e = G.iter_edges_e
  let fold_edges_e = G.fold_edges_e
  let map_vertex = G.map_vertex

  let iter_succ f g v = G.iter_succ f g v; G.iter_pred f g v
  let iter_pred = iter_succ

  let fold_succ f g v a = G.fold_succ f g v (G.fold_pred f g v a)
  let fold_pred = fold_succ

  let iter_succ_e f g v = G.iter_succ_e f g v; G.iter_succ_e f g v
  let fold_succ_e f g v a = G.fold_succ_e f g v (G.fold_pred_e f g v a)
  let iter_pred_e = iter_succ_e
  let fold_pred_e = fold_succ_e
end

module Reverse(G : Graph.Sig.G) :
  (Graph.Sig.G with type t = G.t
                and type V.t = G.V.t
                and type E.t = G.E.t) =
struct
  type t = G.t
  module V = G.V
  type vertex = V.t
  module E = G.E
  type edge = G.E.t
  let is_directed = G.is_directed

  let flip e = E.create (E.dst e) (E.label e) (E.src e)
  let flip_arg f x y = f y x
  let flip_arg_e f e = f (flip e)

  let is_empty = G.is_empty
  let nb_vertex = G.nb_vertex
  let nb_edges = G.nb_edges

  let out_degree = G.in_degree
  let in_degree = G.out_degree

  let mem_vertex = G.mem_vertex
  let mem_edge g x y = G.mem_edge g y x
  let mem_edge_e g e = G.mem_edge_e g (flip e)
  let find_edge g x y = G.find_edge g y x
  let find_all_edges g x y = G.find_all_edges g y x

  let succ = G.pred
  let pred = G.succ
  let succ_e g v = List.map flip (G.pred_e g v)
  let pred_e g v = List.map flip (G.succ_e g v)

  let iter_vertex = G.iter_vertex
  let fold_vertex = G.fold_vertex
  let iter_edges f = G.iter_edges (flip_arg f)
  let fold_edges f = G.fold_edges (flip_arg f)
  let iter_edges_e f = G.iter_edges_e (flip_arg_e f)
  let fold_edges_e f = G.fold_edges_e (flip_arg_e f)
  let map_vertex = G.map_vertex

  let iter_succ = G.iter_pred
  let iter_pred = G.iter_succ

  let fold_succ = G.fold_pred
  let fold_pred = G.fold_succ

  let iter_succ_e f = G.iter_pred_e (flip_arg_e f)
  let fold_succ_e f = G.fold_pred_e (flip_arg_e f)
  let iter_pred_e f = G.iter_succ_e (flip_arg_e f)
  let fold_pred_e f = G.fold_succ_e (flip_arg_e f)
end

module Subgraph(G : Graph.Sig.G) :
  (Graph.Sig.G with type t = G.t * (G.V.t -> bool)
                and type V.t = G.V.t
                and type E.t = G.E.t) =
struct
  type t = G.t * (G.V.t -> bool)
  module V = G.V
  type vertex = V.t
  module E = G.E
  type edge = G.E.t
  let is_directed = G.is_directed

  let sub_apply sub f v a = if sub v then f v a else a
  let sub_apply0 sub f v = if sub v then f v
  let sub_edge sub e = sub (G.E.src e) && sub (G.E.dst e)
  let sub_apply_e sub f e a = if sub_edge sub e then f e a else a
  let sub_apply_e0 sub f e = if sub_edge sub e then f e

  let mem_vertex (g, sub) v = sub v && G.mem_vertex g v
  let mem_edge (g, sub) x y = sub x && sub y && G.mem_edge g y x
  let mem_edge_e (g, sub) e = sub_edge sub e && G.mem_edge_e g e 
  let find_edge (g, sub) x y =
    if sub x && sub y then G.find_edge g y x
    else raise Not_found
  let find_all_edges (g, sub) x y =
    if sub x && sub y then G.find_all_edges g y x
    else raise Not_found


  let succ (g, sub) v = List.filter sub (G.succ g v)
  let pred (g, sub) v = List.filter sub (G.pred g v)
  let succ_e (g, sub) v = List.filter (sub_edge sub) (G.pred_e g v)
  let pred_e (g, sub) v = List.filter (sub_edge sub) (G.succ_e g v)

  let iter_vertex f (g, sub) = G.iter_vertex (fun v -> if sub v then f v) g
  let fold_vertex f (g, sub) = G.fold_vertex (sub_apply sub f) g
  let iter_edges f (g, sub) =
    G.iter_edges (fun s t -> if sub s && sub t then f s t) g
  let fold_edges f (g, sub) =
    G.fold_edges (fun s t a -> if sub s && sub t then f s t a else a) g
  let iter_edges_e f (g, sub) = G.iter_edges_e (sub_apply_e0 sub f) g
  let fold_edges_e f (g, sub) = G.fold_edges_e (sub_apply_e sub f) g
  let map_vertex f (g, sub) =
    (G.map_vertex (fun v -> if sub v then f v else v) g, sub)

  let iter_succ f (g, sub) v = G.iter_succ (sub_apply0 sub f) g v
  let iter_pred f (g, sub) v = G.iter_pred (sub_apply0 sub f) g v

  let fold_succ f (g, sub) v = G.fold_succ (sub_apply sub f) g v
  let fold_pred f (g, sub) v = G.fold_pred (sub_apply sub f) g v

  let iter_succ_e f (g, sub) v = G.iter_succ_e (sub_apply_e0 sub f) g v
  let fold_succ_e f (g, sub) v = G.fold_succ_e (sub_apply_e sub f) g v
  let iter_pred_e f (g, sub) v = G.iter_pred_e (sub_apply_e0 sub f) g v
  let fold_pred_e f (g, sub) v = G.fold_pred_e (sub_apply_e sub f) g v

  let nb_vertex g = fold_vertex (fun _ x -> x + 1) g 0
  let nb_edges g = fold_edges (fun _ _ x-> x + 1) g 0
  let is_empty g = nb_vertex g > 0

  let out_degree g v = fold_succ (fun _ x -> x + 1) g v 0
  let in_degree g v = fold_pred (fun _ x -> x + 1) g v 0
end

type edge_type = TreeEdge | BackEdge | CrossEdge | ForwardEdge

module DfsTree = struct
  module type G = sig
    type t
    module V : Graph.Sig.VERTEX
    module E : Graph.Sig.EDGE with type vertex = V.t
    val iter_succ : (V.t -> unit) -> t -> V.t -> unit
    val fold_succ : (V.t -> 'a -> 'a) -> t -> V.t -> 'a -> 'a
    val nb_vertex : t -> int
    val find_edge : t -> V.t -> V.t -> E.t
    val is_directed : bool
    val iter_edges_e : (E.t -> unit) -> t -> unit
    val iter_vertex : (V.t -> unit) -> t -> unit
  end
  module Make (G : G) = struct
    module HT = Hashtbl.Make(G.V)
    type t = { dfs_num : int HT.t;
               vertex : G.V.t array;
               size : int;
               parent : int array;
               mutable max_dfs : int array option (* computed lazily *)
             }

    let get_dfs_num v tree = HT.find tree.dfs_num v

    let is_root v tree = get_dfs_num v tree = 0

    let size tree = tree.size

    (** Process a DFS tree bottom-up. *)
    let fold_dfs_tree f tree =
      let children = Array.create tree.size [] in
      for v = (tree.size - 1) downto 1 do
        let parent = tree.parent.(v) in
        let value = f (tree.vertex.(v)) (children.(v)) in
        children.(v) <- [];
        children.(parent) <- value::(children.(parent))
      done;
      f (tree.vertex.(0)) children.(0)

    let compute_max_dfs tree =
      match tree.max_dfs with
      | Some max_dfs -> max_dfs
      | None ->
        let max_dfs = Array.create tree.size 0 in
        let f v children =
          let v_dfs = get_dfs_num v tree in
          let v_max = List.fold_left max v_dfs children in
          max_dfs.(v_dfs) <- v_max;
          v_max
        in
        ignore (fold_dfs_tree f tree);
        tree.max_dfs <- Some max_dfs;
        max_dfs

    let is_ancestor s t tree =
      let max_dfs = compute_max_dfs tree in
      let s_num = get_dfs_num s tree in
      let t_num = get_dfs_num t tree in
      s_num <= t_num && (max_dfs.(s_num) >= t_num)

    let parent v tree =
      if is_root v tree then None
      else Some (tree.vertex.(tree.parent.(get_dfs_num v tree)))

    let parent_edge v graph tree =
      if is_root v tree then None
      else begin
        let dfs_num = get_dfs_num v tree in
        let parent = tree.parent.(dfs_num) in
        Some (G.find_edge graph tree.vertex.(parent) v)
      end

    let compute graph init =
      let next = ref 0 in
      let next_dfs_num () =
        let n = !next in
        next := n + 1;
        n
      in
      let size = G.nb_vertex graph in
      let dfs_num = HT.create (2*size) in
      let vertex = Array.create size init in
      let parent = Array.create size 0 in
      let rec dfs v =
        let n = next_dfs_num () in
        let get_dfs_num w =
          try HT.find dfs_num w
          with Not_found -> (* not yet visited *)
            let w_num = dfs w in
            parent.(w_num) <- n;
            w_num
        in

        HT.add dfs_num v n;
        vertex.(n) <- v;
        G.iter_succ (fun w -> ignore (get_dfs_num w)) graph v;
        n
      in
      ignore (dfs init);
      { dfs_num = dfs_num;
        vertex = vertex;
        size = size;
        parent = parent;
        max_dfs = None }

    let classify u v tree =
      let u_num = get_dfs_num u tree in
      let v_num = get_dfs_num v tree in
      if tree.parent.(v_num) = u_num then TreeEdge else begin
        if G.is_directed then begin
          if is_ancestor u v tree then ForwardEdge
          else if is_ancestor v u tree then BackEdge
          else CrossEdge
        end else begin
          if tree.parent.(u_num) = v_num then TreeEdge
          else if u_num < v_num then ForwardEdge
          else BackEdge
        end
      end

    let nop _ = ()

    let iter_dfs_order ?pre:(pre=nop) ?post:(post=nop) tree =
      let rec climb_to_ancestor n dest =
        if n != dest then begin
          post (tree.vertex.(n));
          climb_to_ancestor (tree.parent.(n)) dest
        end
      in
      let last = tree.size - 1 in
      for n = 0 to last - 1 do
        pre (tree.vertex.(n));
        let next_parent = tree.parent.(n + 1) in
        if next_parent != n then climb_to_ancestor n next_parent;
      done;
      pre (tree.vertex.(last));
      climb_to_ancestor last 0;
      post (tree.vertex.(0))

    let vertices tree = BatArray.enum tree.vertex
    let leaves tree =
      let internal = Array.create tree.size false in
      let last = tree.size - 1 in
      let f v =
        if internal.(v) then None
        else Some tree.vertex.(v)
      in
      for i = 0 to last do
        internal.(tree.parent.(i)) <- true
      done;
      BatEnum.filter_map f (BatEnum.range ~until:last 0)

    let fold_tree_succ f graph tree v a =
      let g u a = match classify v u tree with
        | TreeEdge -> f u a
        | _        -> a
      in
      G.fold_succ g graph v a

    let fold_nontree_succ f graph tree v a =
      let g u a = match classify v u tree with
        | TreeEdge -> a
        | _        -> f u a
      in
      G.fold_succ g graph v a

    let fold_backedges f graph tree v a =
      let g u a = match classify v u tree with
        | BackEdge -> f u a
        | _        -> a
      in
      G.fold_succ g graph v a

    let fold_forward_edges f graph tree v a =
      let g u a = match classify v u tree with
        | ForwardEdge -> f u a
        | _           -> a
      in
      G.fold_succ g graph v a

    let fold_crossedges f graph tree v a =
      let g u a = match classify v u tree with
        | CrossEdge -> f u a
        | _         -> a
      in
      G.fold_succ g graph v a

    let fold_edges_dfs_order f a graph tree =
      let f_succ n =
        let v = tree.vertex.(n) in
        fun u a -> (f a v u)
      in
      let rec climb_to_ancestor a n dest =
        if n = dest then a else begin
          let a = fold_nontree_succ (f_succ n) graph tree (tree.vertex.(n)) a in
          climb_to_ancestor a (tree.parent.(n)) dest
        end
      in
      let last = tree.size - 1 in
      let rec visit a n =
        let a = f a (tree.vertex.(tree.parent.(n))) tree.vertex.(n) in
        if n = last then climb_to_ancestor a n 0
        else begin
          let next_parent = tree.parent.(n + 1) in
          let a =
            if next_parent = n then a
            else climb_to_ancestor a n next_parent
          in
          visit a (n + 1)
        end
      in
      let a = visit a 1 in
      fold_nontree_succ (f_succ 0) graph tree (tree.vertex.(0)) a

    let display vstring tree graph =
      let module Display = struct
        include G;;
        open Graph.Graphviz.DotAttributes;;
        let vertex_name v =
          Printf.sprintf "\"#%d: %s\"" (get_dfs_num v tree) (vstring v)
        let get_subgraph v = None
        let default_vertex_attributes _ = []
        let default_edge_attributes _ = []
        let graph_attributes _ = []
        let vertex_attributes _ = []
        let edge_attributes e =
          match classify (G.E.src e) (G.E.dst e) tree with
          | TreeEdge -> [`Label "tree"]
          | CrossEdge -> [`Label "cross"]
          | BackEdge -> [`Label "back"]
          | ForwardEdge -> [`Label "forward"]
      end
      in
      let module DotOutput = Graph.Graphviz.Dot(Display) in
      display_dot DotOutput.output_graph graph
  end
end

module PersistentCopy = struct
  module type G = sig
    type t
    module V : Graph.Sig.VERTEX
    val fold_vertex : (V.t -> 'a -> 'a) -> t -> 'a -> 'a
    val fold_edges : (V.t -> V.t -> 'a -> 'a) -> t -> 'a -> 'a
    val fold_succ : (V.t -> 'a -> 'a) -> t -> V.t -> 'a -> 'a
    val mem_vertex : t -> V.t -> bool
  end
  module Digraph (G : G) = struct
    include Graph.Persistent.Digraph.Concrete(G.V)
    let copy g =
      let gcopy = G.fold_vertex (fun v g -> add_vertex g v) g empty in
      G.fold_edges (fun u v g -> add_edge g u v) g gcopy
    let copy_reachable init g =
      let rec go (worklist, pg) =
        match worklist with
        | [] -> pg
        | (v::worklist) ->
          let f succ (worklist, pg) =
            let h = add_edge pg v succ in
            if mem_vertex pg succ then (worklist, h)
            else (succ::worklist, h)
          in
          go (G.fold_succ f g v (worklist, pg))
      in
      if G.mem_vertex g init
      then add_vertex (go ([init], empty)) init
      else empty
  end
end

module Display = struct
  module type G = sig
    type t
    module V : Graph.Sig.VERTEX
    module E : Graph.Sig.EDGE with type vertex = V.t
    val iter_vertex : (V.t -> unit) -> t -> unit
    val iter_edges_e : (E.t -> unit) -> t -> unit
  end
  module Make
      (G : G)
      (S : Putil.S with type t = G.V.t)
      (D : sig
         val graph_attributes : G.t -> Graph.Graphviz.DotAttributes.graph list
         val vertex_attributes : G.V.t -> Graph.Graphviz.DotAttributes.vertex list
         val edge_attributes : G.E.t -> Graph.Graphviz.DotAttributes.edge list
       end) :
  sig
    val output_graph : out_channel -> G.t -> unit
    val display : G.t -> unit
  end = struct
    module Display = struct
      include D
      include G
      let vertex_name x = "\"" ^ (String.escaped (S.show x)) ^ "\""
      let get_subgraph v =  None
      let default_vertex_attributes _ = []
      let default_edge_attributes _ = []
    end
    module Out = Graph.Graphviz.Dot(Display)
    let output_graph = Out.output_graph
    let display g = display_dot Out.output_graph g
  end

  module MakeSimple (G : G) (S : Putil.S with type t = G.V.t) =
    Make(G)(S)(struct
      let graph_attributes _ = []
      let vertex_attributes _ = []
      let edge_attributes _ = []
    end)

  module MakeLabeled
      (G : G)
      (Show_vertex : Putil.S with type t = G.V.t)
      (Show_edge : Putil.S with type t = G.E.label) =
    Make(G)(Show_vertex)(struct
      let graph_attributes _ = []
      let vertex_attributes _ = []
      let edge_attributes e =
        [`Label (String.escaped (Show_edge.show (G.E.label e)))]
    end)

  module MakeStructural (G : G) = struct
    module M = Memo.Make(G.V)
    let output_graph g =
      let id = ref (-1) in
      let name = M.memo (fun _ -> incr id; !id) in
      let module Show_v = struct
        type t = G.V.t
        include Putil.MakeFmt(struct
            type a = t
            let format formatter v = Format.pp_print_int formatter (name v)
          end)
      end
      in
      let module D = MakeSimple(G)(Show_v) in
      D.output_graph g

    let display g = display_dot output_graph g
  end
end

module Unfold = struct
  module type G = sig
    type t
    module V : Graph.Sig.VERTEX
    val empty : t
    val add_vertex : t -> V.t -> t
    val add_edge : t -> V.t -> V.t -> t
    val mem_vertex : t -> V.t -> bool
    val fold_succ : (V.t -> 'a -> 'a) -> t -> V.t -> 'a -> 'a
  end
  module Make (G : G) = struct
    let unfold init succ =
      let add_vertex v (worklist, g) =
        if G.mem_vertex g v then (worklist, g)
        else (v::worklist, G.add_vertex g v)
      in
      let add_succ u (worklist,g) v =
        let (worklist, g) = add_vertex v (worklist, g) in
        (worklist, G.add_edge g u v)
      in
      let rec fix (worklist, g) =
        match worklist with
        | [] -> g
        | (v::worklist) ->
          fix (BatEnum.fold (add_succ v) (worklist, g) (succ v))
      in
      fix ([init], G.add_vertex G.empty init)

    let forward_reachable g init =
      let succ v = BatList.enum (G.fold_succ (fun v vs -> v::vs) g v []) in
      unfold init succ
  end
end

module Slice = struct
  module type G = sig
    type t
    module V : Graph.Sig.VERTEX
    module E : Graph.Sig.EDGE with type vertex = V.t
    val fold_succ : (V.t -> 'a -> 'a) -> t -> V.t -> 'a -> 'a
    val fold_pred : (V.t -> 'a -> 'a) -> t -> V.t -> 'a -> 'a
  end
  module Make (G : G) = struct
    module VSet = BatSet.Make(G.V)

    let neighborhood g v n =
      let rec go_backward v nbd n =
        let f v nbd =
          if VSet.mem v nbd then nbd else go_backward v (VSet.add v nbd) (n-1)
        in
        if n > 0 then G.fold_pred f g v nbd else nbd
      in
      let rec go_forward v nbd n =
        let f v nbd =
          if VSet.mem v nbd then nbd else go_forward v (VSet.add v nbd) (n-1)
        in
        if n > 0 then G.fold_succ f g v nbd else nbd
      in
      let start = VSet.singleton v in
      let forward_nbd = go_forward v start n in
      let backward_nbd = go_backward v start n in
      let nbd = VSet.union forward_nbd backward_nbd in
      fun v -> VSet.mem v nbd

    let reachable fold_succ g start =
      let go (worklist, reach) =
        match worklist with
        | [] -> None
        | (v::worklist) ->
          let f succ (worklist, reach) =
            if VSet.mem succ reach then (worklist, reach)
            else (succ::worklist, VSet.add succ reach)
          in
          try
            Some (v, fold_succ f g v (worklist, reach))
          with Invalid_argument _ -> raise (Invalid_argument "[apak] reachable")
      in
      BatEnum.unfold start go

    let reachable_vertices fold_succ g start =
      let rec go (worklist, reach) =
        match worklist with
        | [] -> reach
        | (v::worklist) ->
          let f succ (worklist, reach) =
            if VSet.mem succ reach then (worklist, reach)
            else (succ::worklist, VSet.add succ reach)
          in
          go (fold_succ f g v (worklist, reach))
      in
      go start

    let forward_reachable g v = reachable G.fold_succ g ([v], VSet.singleton v)
    let backward_reachable g v = reachable G.fold_pred g ([v], VSet.singleton v)

    let forward_reachable_set g vs =
      reachable G.fold_succ g (vs, VSet.of_enum (BatList.enum vs))
    let backward_reachable_set g vs =
      reachable G.fold_pred g (vs, VSet.of_enum (BatList.enum vs))

    let chop g s t =
      let reachable =
        reachable_vertices G.fold_succ g ([s], VSet.singleton s)
      in
      BatEnum.filter (fun x -> VSet.mem x reachable) (backward_reachable g t)

    let chop_set g ss ts =
      let reachable =
        reachable_vertices G.fold_succ g (ss, VSet.of_enum (BatList.enum ss))
      in
      BatEnum.filter
        (fun x -> VSet.mem x reachable)
        (backward_reachable_set g ts)
  end
end

module Traverse = struct
  module type G = sig
    val is_directed : bool
    type t
    module V: Graph.Sig.COMPARABLE
    val iter_vertex : (V.t -> unit) -> t -> unit
    val fold_vertex : (V.t -> 'a -> 'a) -> t -> 'a -> 'a
    val iter_succ : (V.t -> unit) -> t -> V.t -> unit
    val fold_succ : (V.t -> 'a -> 'a) -> t -> V.t -> 'a -> 'a
  end
  module Make (G : G) = struct
    module Dfs = Graph.Traverse.Dfs(G)

    let reverse_postorder v g =
      let vertices = ref [] in
      let add_vertex v = vertices := v::(!vertices) in
      Dfs.postfix_component add_vertex g v;
      BatList.enum (List.rev (!vertices))
  end
end

module Build = struct
  module type G = sig
    type t
    type vertex
    val remove_vertex : t -> vertex -> t
    val enum_pred : t -> vertex -> vertex BatEnum.t
    val enum_succ : t -> vertex -> vertex BatEnum.t
    val add_edge : t -> vertex -> vertex -> t
  end

  module Make(G : G) = struct
    let split g v ~pred:pred ~succ:succ =
      let predecessors = G.enum_pred g v in
      let successors = G.enum_succ g v in
      let g = G.remove_vertex g v in
      let g = G.add_edge g pred succ in
      let g = BatEnum.fold (fun g p -> G.add_edge g p pred) g predecessors in
      BatEnum.fold (fun g s -> G.add_edge g succ s) g successors

    let eliminate_vertex g v =
      let predecessors = G.enum_pred g v in
      let successors = G.enum_succ g v in
      let g = G.remove_vertex g v in
      let add_edge g (u, v) = G.add_edge g u v in
      BatEnum.fold add_edge g (Putil.cartesian_product predecessors successors)
  end
end
