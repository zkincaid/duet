open BatPervasives

module type Tagged = sig
  include Putil.S
  val tag : t -> int
end

(* The following two modules are taken from Jean-Christophe Filliatre's
   implementation of Patricia trees (ptset.ml and ptmap.ml), with minor
   modifications.  *)

(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) Jean-Christophe Filliatre                               *)
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
module PTSet (T : Tagged) : Putil.Hashed.Set.S with type elt = T.t = struct

  (*s Sets of integers implemented as Patricia trees, following Chris Okasaki
    and Andrew Gill's paper {\em Fast Mergeable Integer Maps} ({\tt\small
    http://www.cs.columbia.edu/\~{}cdo/papers.html\#ml98maps}).  Patricia
    trees provide faster operations than standard library's module [Set], and
    especially very fast [union], [subset], [inter] and [diff] operations. *)

  (*s The idea behind Patricia trees is to build a {\em trie} on the binary
    digits of the elements, and to compact the representation by branching only
    one the relevant bits (i.e. the ones for which there is at least on element
    in each subtree). We implement here {\em little-endian} Patricia trees: bits
    are processed from least-significant to most-significant. The trie is
    implemented by the following type [t]. [Empty] stands for the empty trie,
    and [Leaf k] for the singleton [k]. (Note that [k] is the actual element.)
    [Branch (m,p,l,r)] represents a branching, where [p] is the prefix (from the
    root of the trie) and [m] is the branching bit (a power of 2). [l] and [r]
    contain the subsets for which the branching bit is respectively 0 and
    1. Invariant: the trees [l] and [r] are not empty. *)

  type elt = T.t
  type t =
    | Empty
    | Leaf of elt
    | Branch of int * int * t * t

  (*s Example: the representation of the set $\{1,4,5\}$ is
    $$\mathtt{Branch~(0,~1,~Leaf~4,~Branch~(1,~4,~Leaf~1,~Leaf~5))}$$ The first
    branching bit is the bit 0 (and the corresponding prefix is [0b0], not of
    use here), with $\{4\}$ on the left and $\{1,5\}$ on the right. Then the
    right subtree branches on bit 2 (and so has a branching value of $2^2 = 4$),
    with prefix [0b01 = 1]. *)

  (*s Empty set and singletons. *)

  let tag = T.tag

  let empty = Empty

  let is_empty = function Empty -> true | _ -> false

  let singleton k = Leaf k

  (*s Testing the occurrence of a value is similar to the search in a binary
    search tree, where the branching bit is used to select the appropriate
    subtree. *)

  let zero_bit k m = (k land m) == 0

  let rec mem k = function
    | Empty -> false
    | Leaf j -> (tag k) == (tag j)
    | Branch (_, m, l, r) -> mem k (if zero_bit (tag k) m then l else r)

(*s The following operation [join] will be used in both insertion and
  union. Given two non-empty trees [t0] and [t1] with longest common
  prefixes [p0] and [p1] respectively, which are supposed to
  disagree, it creates the union of [t0] and [t1]. For this, it
  computes the first bit [m] where [p0] and [p1] disagree and create
  a branching node on that bit. Depending on the value of that bit
  in [p0], [t0] will be the left subtree and [t1] the right one, or
  the converse. Computing the first branching bit of [p0] and [p1]
  uses a nice property of twos-complement representation of integers. *)

  let lowest_bit x = x land (-x)

  let branching_bit p0 p1 = lowest_bit (p0 lxor p1)

  let mask p m = p land (m-1)

  let join (p0,t0,p1,t1) =
    let m = branching_bit p0 p1 in
    if zero_bit p0 m then 
      Branch (mask p0 m, m, t0, t1)
    else 
      Branch (mask p0 m, m, t1, t0)

  (*s Then the insertion of value [k] in set [t] is easily implemented using
    [join].  Insertion in a singleton is just the identity or a call to
    [join], depending on the value of [k].  When inserting in a branching
    tree, we first check if the value to insert [k] matches the prefix [p]: if
    not, [join] will take care of creating the above branching; if so, we just
    insert [k] in the appropriate subtree, depending of the branching bit. *)

  let match_prefix k p m = (mask k m) == p

  let add k t =
    let rec ins = function
      | Empty -> Leaf k
      | Leaf j as t -> 
	if (tag j) == (tag k) then t else join (tag k, Leaf k, tag j, t)
      | Branch (p,m,t0,t1) as t ->
	if match_prefix (tag k) p m then
	  if zero_bit (tag k) m then 
	    Branch (p, m, ins t0, t1)
	  else
	    Branch (p, m, t0, ins t1)
	else
	  join (tag k, Leaf k, p, t)
    in
    ins t

  (*s The code to remove an element is basically similar to the code of
    insertion. But since we have to maintain the invariant that both subtrees of
    a [Branch] node are non-empty, we use here the ``smart constructor''
    [branch] instead of [Branch]. *)

  let branch = function
    | (_,_,Empty,t) -> t
    | (_,_,t,Empty) -> t
    | (p,m,t0,t1)   -> Branch (p,m,t0,t1)

  let remove k t =
    let rec rmv = function
      | Empty -> Empty
      | Leaf j as t -> if (tag k) == (tag j) then Empty else t
      | Branch (p,m,t0,t1) as t -> 
	if match_prefix (tag k) p m then
	  if zero_bit (tag k) m then
	    branch (p, m, rmv t0, t1)
	  else
	    branch (p, m, t0, rmv t1)
	else
	  t
    in
    rmv t

  (*s One nice property of Patricia trees is to support a fast union operation
    (and also fast subset, difference and intersection operations). When merging
    two branching trees we examine the following four cases: (1) the trees have
    exactly the same prefix; (2/3) one prefix contains the other one; and (4)
    the prefixes disagree. In cases (1), (2) and (3) the recursion is immediate;
    in case (4) the function [join] creates the appropriate branching. *)

  let rec merge = function
    | Empty, t  -> t
    | t, Empty  -> t
    | Leaf k, t -> add k t
    | t, Leaf k -> add k t
    | (Branch (p,m,s0,s1) as s), (Branch (q,n,t0,t1) as t) ->
      if m == n && match_prefix q p m then
	(* The trees have the same prefix. Merge the subtrees. *)
	Branch (p, m, merge (s0,t0), merge (s1,t1))
      else if m < n && match_prefix q p m then
	(* [q] contains [p]. Merge [t] with a subtree of [s]. *)
	if zero_bit q m then 
	  Branch (p, m, merge (s0,t), s1)
        else 
	  Branch (p, m, s0, merge (s1,t))
      else if m > n && match_prefix p q n then
	(* [p] contains [q]. Merge [s] with a subtree of [t]. *)
	if zero_bit p n then
	  Branch (q, n, merge (s,t0), t1)
	else
	  Branch (q, n, t0, merge (s,t1))
      else
	(* The prefixes disagree. *)
	join (p, s, q, t)

  let union s t = merge (s,t)

  (*s When checking if [s1] is a subset of [s2] only two of the above four
    cases are relevant: when the prefixes are the same and when the prefix of
    [s1] contains the one of [s2], and then the recursion is obvious. In the
    other two cases, the result is [false]. *)

  let rec subset s1 s2 = match (s1,s2) with
    | Empty, _ -> true
    | _, Empty -> false
    | Leaf k1, _ -> mem k1 s2
    | Branch _, Leaf _ -> false
    | Branch (p1,m1,l1,r1), Branch (p2,m2,l2,r2) ->
      if m1 == m2 && p1 == p2 then
	subset l1 l2 && subset r1 r2
      else if m1 > m2 && match_prefix p1 p2 m2 then
	if zero_bit p1 m2 then 
	  subset l1 l2 && subset r1 l2
	else 
	  subset l1 r2 && subset r1 r2
      else
	false

  (*s To compute the intersection and the difference of two sets, we still
    examine the same four cases as in [merge]. The recursion is then
    obvious. *)

  let rec inter s1 s2 = match (s1,s2) with
    | Empty, _ -> Empty
    | _, Empty -> Empty
    | Leaf k1, _ -> if mem k1 s2 then s1 else Empty
    | _, Leaf k2 -> if mem k2 s1 then s2 else Empty
    | Branch (p1,m1,l1,r1), Branch (p2,m2,l2,r2) ->
      if m1 == m2 && p1 == p2 then 
	merge (inter l1 l2, inter r1 r2)
      else if m1 < m2 && match_prefix p2 p1 m1 then
	inter (if zero_bit p2 m1 then l1 else r1) s2
      else if m1 > m2 && match_prefix p1 p2 m2 then
	inter s1 (if zero_bit p1 m2 then l2 else r2)
      else
	Empty

  let rec diff s1 s2 = match (s1,s2) with
    | Empty, _ -> Empty
    | _, Empty -> s1
    | Leaf k1, _ -> if mem k1 s2 then Empty else s1
    | _, Leaf k2 -> remove k2 s1
    | Branch (p1,m1,l1,r1), Branch (p2,m2,l2,r2) ->
      if m1 == m2 && p1 == p2 then
	merge (diff l1 l2, diff r1 r2)
      else if m1 < m2 && match_prefix p2 p1 m1 then
	if zero_bit p2 m1 then 
	  merge (diff l1 s2, r1) 
	else 
	  merge (l1, diff r1 s2)
      else if m1 > m2 && match_prefix p1 p2 m2 then
	if zero_bit p1 m2 then diff s1 l2 else diff s1 r2
      else
	s1

  (*s All the following operations ([cardinal], [iter], [fold], [for_all],
    [exists], [filter], [partition], [choose], [elements]) are implemented as
    for any other kind of binary trees. *)

  let rec cardinal = function
    | Empty -> 0
    | Leaf _ -> 1
    | Branch (_,_,t0,t1) -> cardinal t0 + cardinal t1

  let rec iter f = function
    | Empty -> ()
    | Leaf k -> f k
    | Branch (_,_,t0,t1) -> iter f t0; iter f t1
      
  let rec fold f s accu = match s with
    | Empty -> accu
    | Leaf k -> f k accu
    | Branch (_,_,t0,t1) -> fold f t0 (fold f t1 accu)

  let rec for_all p = function
    | Empty -> true
    | Leaf k -> p k
    | Branch (_,_,t0,t1) -> for_all p t0 && for_all p t1

  let rec exists p = function
    | Empty -> false
    | Leaf k -> p k
    | Branch (_,_,t0,t1) -> exists p t0 || exists p t1

  let rec filter pr = function
    | Empty -> Empty
    | Leaf k as t -> if pr k then t else Empty
    | Branch (p,m,t0,t1) -> branch (p, m, filter pr t0, filter pr t1)

  let partition p s =
    let rec part (t,f as acc) = function
      | Empty -> acc
      | Leaf k -> if p k then (add k t, f) else (t, add k f)
      | Branch (_,_,t0,t1) -> part (part acc t0) t1
    in
    part (Empty, Empty) s

  let rec choose = function
    | Empty -> raise Not_found
    | Leaf k -> k
    | Branch (_, _,t0,_) -> choose t0   (* we know that [t0] is non-empty *)

  let elements s =
    let rec elements_aux acc = function
      | Empty -> acc
      | Leaf k -> k :: acc
      | Branch (_,_,l,r) -> elements_aux (elements_aux acc l) r
    in
    elements_aux [] s

  (*s There is no way to give an efficient implementation of [min_elt] and
    [max_elt], as with binary search trees.  The following implementation is a
    traversal of all elements, barely more efficient than [fold min t (choose
    t)] (resp. [fold max t (choose t)]). Note that we use the fact that there
    is no constructor [Empty] under [Branch] and therefore always a minimal
    (resp. maximal) element there. *)

  let rec min_elt = function
    | Empty -> raise Not_found
    | Leaf k -> k
    | Branch (_,_,s,t) -> min (min_elt s) (min_elt t)

  let rec max_elt = function
    | Empty -> raise Not_found
    | Leaf k -> k
    | Branch (_,_,s,t) -> max (max_elt s) (max_elt t)

  (*s Another nice property of Patricia trees is to be independent of the
    order of insertion. As a consequence, two Patricia trees have the same
    elements if and only if they are structurally equal. *)
      
  let rec compare left right = match left,right with
    | Empty, Empty -> 0
    | Empty, _ -> 1
    | _, Empty -> -1
    | Leaf k0, Leaf k1 -> Pervasives.compare (tag k0) (tag k1)
    | Leaf _, _ -> 1
    | _, Leaf _ -> -1
    | Branch (p,m,s0,s1), Branch (q,n,t0,t1) -> begin
      match Pervasives.compare m n with
	| 0 -> begin match Pervasives.compare p q with
	    | 0 -> begin match compare s0 t0 with
		| 0 -> compare s1 t1
		| other -> other
	    end
	    | other -> other
	end 
	| other -> other
    end

  let rec equal left right = match left, right with
    | Empty, Empty -> true
    | Leaf k0, Leaf k1 -> (tag k0) == (tag k1)
    | Branch (p, m, s0, s1), Branch (q, n, t0, t1) ->
      p == q && m == n && equal s0 t0 && equal s1 t1
    | _, _ -> false

  let rec hash = function
    | Empty -> 543159235
    | Leaf k -> Hashtbl.hash (tag k, 1)
    | Branch (_,_,left,right) -> Hashtbl.hash (hash left, hash right, 2)

  (*i*)
  let make l = List.fold_right add l empty
  (*i*)
    
  (*s Additional functions w.r.t to [Set.S]. *)

  let rec intersect s1 s2 = match (s1,s2) with
    | Empty, _ -> false
    | _, Empty -> false
    | Leaf k1, _ -> mem k1 s2
    | _, Leaf k2 -> mem k2 s1
    | Branch (p1,m1,l1,r1), Branch (p2,m2,l2,r2) ->
      if m1 == m2 && p1 == p2 then
        intersect l1 l2 || intersect r1 r2
      else if m1 < m2 && match_prefix p2 p1 m1 then
        intersect (if zero_bit p2 m1 then l1 else r1) s2
      else if m1 > m2 && match_prefix p1 p2 m2 then
        intersect s1 (if zero_bit p1 m2 then l2 else r2)
      else
        false

  (* Extra operations *)

  let enum t =
    let rec pull acc = function
      | [] -> raise BatEnum.No_more_elements
      | Empty::ts -> pull acc ts
      | Leaf elt::ts -> (elt, List.rev_append acc ts)
      | Branch (_, _, t0, t1)::ts -> pull acc (t0::(t1::ts))
    in
    let add_cardinal sum t = sum + (cardinal t) in
    let rec make ts count =
      BatEnum.make
	~next:(fun () ->
	  let (hd, tl) = pull [] (!ts) in
	  decr count;
	  ts := tl;
	  hd)

	~count:(fun () ->
	  if !count < 0 then count := (List.fold_left add_cardinal 0 (!ts));
	  !count)

	~clone:(fun () ->
	  make (ref !ts) (ref !count))
    in
    make (ref [t]) (ref (-1))

  let of_enum enum = BatEnum.fold (fun set elt -> add elt set) empty enum

  let map f s = fold (fun v set -> add (f v) set) s empty

  let rec filter_map f s = 
    let add v set =
      match f v with
	| Some u -> add u set
	| None -> set
    in
    fold add s empty

  let pop s =
    let elt = min_elt s in
    (elt, remove elt s)

  include Putil.MakeFmt(struct
    type a = t
    let format formatter set =
      let enum = enum set in
      Putil.format_enum T.format ~left:"{" ~sep:"," ~right:"}" formatter enum
  end)
  module Compare_t = struct
    type a = t
    let compare = compare
  end
end

module PTMap (T : Tagged) : Putil.Map.S with type key = T.t = struct

(*s Maps of integers implemented as Patricia trees, following Chris
    Okasaki and Andrew Gill's paper {\em Fast Mergeable Integer Maps}
    ({\tt\small http://www.cs.columbia.edu/\~{}cdo/papers.html\#ml98maps}).
    See the documentation of module [Ptset] which is also based on the
    same data-structure. *)

  type key = T.t
  type 'a t =
    | Empty
    | Leaf of (key * 'a)
    | Branch of int * int * 'a t * 'a t

  let tag = T.tag

  let empty = Empty

  let zero_bit k m = (k land m) == 0

  let rec mem k = function
    | Empty -> false
    | Leaf (j,_) -> tag k == tag j
    | Branch (_, m, l, r) -> mem k (if zero_bit (tag k) m then l else r)

  let rec find k = function
    | Empty -> raise Not_found
    | Leaf (j,x) -> if (tag k) == (tag j) then x else raise Not_found
    | Branch (_, m, l, r) -> find k (if zero_bit (tag k) m then l else r)

  let lowest_bit x = x land (-x)

  let branching_bit p0 p1 = lowest_bit (p0 lxor p1)

  let mask p m = p land (m-1)

  let join (p0,t0,p1,t1) =
    let m = branching_bit p0 p1 in
    if zero_bit p0 m then 
      Branch (mask p0 m, m, t0, t1)
    else 
      Branch (mask p0 m, m, t1, t0)

  let match_prefix k p m = (mask k m) == p

  let add k x t =
    let rec ins = function
      | Empty -> Leaf (k,x)
      | Leaf (j,_) as t -> 
	if tag j == tag k then 
	  Leaf (k,x) 
	else 
	  join (tag k, Leaf (k,x), tag j, t)
      | Branch (p,m,t0,t1) as t ->
	if match_prefix (tag k) p m then
	  if zero_bit (tag k) m then 
	    Branch (p, m, ins t0, t1)
	  else
	    Branch (p, m, t0, ins t1)
	else
	  join (tag k, Leaf (k,x), p, t)
    in
    ins t

  let branch = function
    | (_,_,Empty,t) -> t
    | (_,_,t,Empty) -> t
    | (p,m,t0,t1)   -> Branch (p,m,t0,t1)

  let get_prefix = function
    | Empty -> assert false
    | Leaf (k,_) -> tag k
    | Branch (p,_,_,_) -> p

  let join_safe = function
    | (t, Empty) | (Empty, t) -> t
    | (t0, t1) ->
      let p0 = get_prefix t0 in
      let p1 = get_prefix t1 in
      let m = branching_bit p0 p1 in
      if zero_bit p0 m then
	Branch (mask p0 m, m, t0, t1)
      else
	Branch (mask p0 m, m, t1, t0)

  let remove k t =
    let rec rmv = function
      | Empty -> Empty
      | Leaf (j,_) as t -> if tag k == tag j then Empty else t
      | Branch (p,m,t0,t1) as t -> 
	if match_prefix (tag k) p m then
	  if zero_bit (tag k) m then
	    branch (p, m, rmv t0, t1)
	  else
	    branch (p, m, t0, rmv t1)
	else
	  t
    in
    rmv t

  let rec iter f = function
    | Empty -> ()
    | Leaf (k,x) -> f k x
    | Branch (_,_,t0,t1) -> iter f t0; iter f t1

  let rec map f = function
    | Empty -> Empty
    | Leaf (k,x) -> Leaf (k, f x)
    | Branch (p,m,t0,t1) -> Branch (p, m, map f t0, map f t1)
      
  let rec mapi f = function
    | Empty -> Empty
    | Leaf (k,x) -> Leaf (k, f k x)
    | Branch (p,m,t0,t1) -> Branch (p, m, mapi f t0, mapi f t1)
      
  let rec fold f s accu = match s with
    | Empty -> accu
    | Leaf (k,x) -> f k x accu
    | Branch (_,_,t0,t1) -> fold f t0 (fold f t1 accu)

  let rec cardinal = function
    | Empty -> 0
    | Leaf (_, _) -> 1
    | Branch (_, _, t0, t1) -> (cardinal t0) + (cardinal t1)

  let enum t =
    let rec pull acc = function
      | [] -> raise BatEnum.No_more_elements
      | Empty::ts -> pull acc ts
      | Leaf (k,v)::ts -> ((k,v), List.rev_append acc ts)
      | Branch (_, _, t0, t1)::ts -> pull acc (t0::(t1::ts))
    in
    let add_cardinal sum t = sum + (cardinal t) in
    let rec make ts count =
      BatEnum.make
	~next:(fun () ->
	  let (hd, tl) = pull [] (!ts) in
	  decr count;
	  ts := tl;
	  hd)

	~count:(fun () ->
	  if !count < 0 then count := (List.fold_left add_cardinal 0 (!ts));
	  !count)

	~clone:(fun () ->
	  make (ref !ts) (ref !count))
    in
    make (ref [t]) (ref (-1))

  let keys map = enum map /@ fst
  let values map = enum map /@ snd
  let bindings map = BatList.of_enum (enum map)
  let singleton k v = Leaf (k, v)
  let is_empty = function
    | Empty -> true
    | _     -> false

  let rec for_all p = function
    | Empty -> true
    | Leaf (k, v) -> p k v
    | Branch (_,_,t0,t1) -> for_all p t0 && for_all p t1

  let rec exists p = function
    | Empty -> false
    | Leaf (k, v) -> p k v
    | Branch (_,_,t0,t1) -> exists p t0 || exists p t1

  let partition p s =
    let rec part (t,f as acc) = function
      | Empty -> acc
      | Leaf (k,v) -> if p k v then (add k v t, f) else (t, add k v f)
      | Branch (_,_,t0,t1) -> part (part acc t0) t1
    in
    part (Empty, Empty) s

  let rec choose = function
    | Empty -> raise Not_found
    | Leaf k -> k
    | Branch (_, _,t0,_) -> choose t0   (* we know that [t0] is non-empty *)

  let of_enum enum = BatEnum.fold (fun m (k,v) -> add k v m) empty enum

  let rec filter pr = function
    | Empty -> Empty
    | Leaf (_,v) as t -> if pr v then t else Empty
    | Branch (p,m,t0,t1) -> branch (p, m, filter pr t0, filter pr t1)

  let rec filterv pr = function
    | Empty -> Empty
    | Leaf (_,v) as t -> if pr v then t else Empty
    | Branch (p,m,t0,t1) -> branch (p, m, filter pr t0, filter pr t1)

  let rec filter pr = function
    | Empty -> Empty
    | Leaf (k,v) as t -> if pr k v then t else Empty
    | Branch (p,m,t0,t1) -> branch (p, m, filter pr t0, filter pr t1)

  let rec filter_map f = function
    | Empty -> Empty
    | Leaf (k,v) -> begin match f k v with
	| Some r -> Leaf (k, r)
	| None -> Empty
    end
    | Branch (p,m,t0,t1) -> branch (p, m, filter_map f t0, filter_map f t1)

  let merge f s t =
    let map_left = filter_map (fun k x -> f k (Some x) None) in
    let map_right = filter_map (fun k x -> f k None (Some x)) in
    let rec go = function
      | Empty, t -> map_right t
      | t, Empty -> map_left t

      | (Leaf (j,v0), Leaf(k,v1)) ->
	if tag j == tag k then begin
	  match f j (Some v0) (Some v1) with
	    | Some r -> Leaf (j, r)
	    | None -> Empty
	end else begin
	  match f j (Some v0) None, f k None (Some v1) with
	    | None, None -> Empty
	    | Some r, None -> Leaf (j, r)
	    | None, Some r -> Leaf (k, r)
	    | Some r0, Some r1 ->
	      join (tag j, Leaf (j, r0), tag k, Leaf (k, r1))
	end

      | ((Leaf (k,v) as left), (Branch (p,m,s0,s1) as t)) ->
	if match_prefix (tag k) p m then
	  if zero_bit (tag k) m then
	    branch (p, m, go (left, s0), map_right s1)
	  else
	    branch (p, m, map_right s0, go (left, s1))
	else begin
	  match f k (Some v) None with
	    | Some r -> join_safe (Leaf (k, r), map_right t)
	    | None -> map_right t
	end

      | ((Branch (p,m,s0,s1) as t), (Leaf (k,v) as right)) ->
	if match_prefix (tag k) p m then
	  if zero_bit (tag k) m then
	    branch (p, m, go (s0, right), map_left s1)
	  else
	    branch (p, m, map_left s0, go (s1, right))
	else begin
	  match f k None (Some v) with
	    | Some r -> join_safe (Leaf (k, r), map_left t)
	    | None -> map_left t
	end

      | (Branch (p,m,s0,s1) as s), (Branch (q,n,t0,t1) as t) ->
	if m == n && match_prefix q p m then
	(* The trees have the same prefix. Merge the subtrees. *)
	  Branch (p, m, go (s0,t0), go (s1,t1))
	else if m < n && match_prefix q p m then
	(* [q] contains [p]. Merge [t] with a subtree of [s]. *)
	  if zero_bit q m then 
	    branch (p, m, go (s0,t), map_left s1)
          else 
	    branch (p, m, map_left s0, go (s1,t))
	else if m > n && match_prefix p q n then
	(* [p] contains [q]. Merge [s] with a subtree of [t]. *)
	  if zero_bit p n then
	    branch (q, n, go (s,t0), map_right t1)
	  else
	    branch (q, n, map_right t0, go (s,t1))
	else
	(* The prefixes disagree. *)
	  join_safe (map_left s, map_right t)
    in
    go (s, t)

  let rec hash hv = function
    | Empty -> 0
    | Leaf (k,v) -> Hashtbl.hash (tag k, hv v)
    | Branch (_,_,left,right) -> Hashtbl.hash (hash hv left, hash hv right)

  let rec compare cmp left right = match left,right with
    | Empty, Empty -> 0
    | Empty, _ -> 1
    | _, Empty -> -1
    | Leaf (k0,v0), Leaf (k1,v1) -> begin
      match Pervasives.compare (tag k0) (tag k1) with
	| 0     -> cmp v0 v1
	| other -> other
    end
    | Leaf (_,_), _ -> 1
    | _, Leaf (_,_) -> -1
    | Branch (p,m,s0,s1), Branch (q,n,t0,t1) -> begin
      match Pervasives.compare m n with
	| 0 -> begin match Pervasives.compare p q with
	    | 0 -> begin match compare cmp s0 t0 with
		| 0 -> compare cmp s1 t1
		| other -> other
	    end
	    | other -> other
	end 
	| other -> other
    end

  let rec equal eq left right = match left, right with
    | Empty, Empty -> true
    | Leaf (k0, v0), Leaf (k1,v1) -> (tag k0) == (tag k1) && eq v0 v1
    | Branch (p, m, s0, s1), Branch (q, n, t0, t1) ->
      p == q && m == n && equal eq s0 t0 && equal eq s1 t1
    | _, _ -> false

  let rec min_binding = function
    | Empty -> raise Not_found
    | Leaf (k, v) -> (k, v)
    | Branch (_, _, t, _) -> min_binding t

  let rec max_binding = function
    | Empty -> raise Not_found
    | Leaf (k, v) -> (k, v)
    | Branch (_, _, _, t) -> max_binding t

  let format pp_val formatter map =
    let pp formatter (key, value) =
      Format.pp_open_box formatter 0;
      T.format formatter key;
      Format.pp_print_string formatter " => ";
      pp_val formatter value;
      Format.pp_close_box formatter ();
    in
    Putil.format_enum pp formatter (enum map)
end

module MakeCoreType (T : Tagged) : sig
  include Putil.CoreType with type t = T.t
  val tag : t -> int
end = struct
  include T
  module Compare_t = struct
    type a = t
    let compare x y = compare (tag x) (tag y)
  end
  module Set = PTSet(T)
  module Map = PTMap(T)
  module HT = BatHashtbl.Make(struct
    type t = T.t
    let hash x = Hashtbl.hash (tag x)
    let equal x y = (tag x) = (tag y)
  end)
  let compare = Compare_t.compare
  let hash x = Hashtbl.hash (tag x)
  let equal x y = (tag x) = (tag y)
end
