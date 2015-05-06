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

(*i $Id: hmap.ml,v 1.5 2008-07-21 14:53:06 filliatr Exp $ i*)

(*s Maps of integers implemented as Patricia trees, following Chris
    Okasaki and Andrew Gill's paper {\em Fast Mergeable Integer Maps}
    ({\tt\small http://www.cs.columbia.edu/\~{}cdo/papers.html\#ml98maps}).
    See the documentation of module [Ptset] which is also based on the
    same data-structure. *)

open Hashcons

type 'a key = 'a hash_consed

type ('a, 'b) t =
  | Empty
  | Leaf of 'a key * 'b
  | Branch of int * int * ('a, 'b) t * ('a, 'b) t

let empty = Empty

let zero_bit k m = (k land m) == 0

let rec mem k = function
  | Empty -> false
  | Leaf (j,_) -> k.tag == j.tag
  | Branch (_, m, l, r) -> mem k (if zero_bit k.tag m then l else r)

let rec find k = function
  | Empty -> raise Not_found
  | Leaf (j,x) -> if k.tag == j.tag then x else raise Not_found
  | Branch (_, m, l, r) -> find k (if zero_bit k.tag m then l else r)

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
      if j.tag == k.tag then
        Leaf (k,x)
      else
        join (k.tag, Leaf (k,x), j.tag, t)
    | Branch (p,m,t0,t1) as t ->
      if match_prefix k.tag p m then
        if zero_bit k.tag m then
          Branch (p, m, ins t0, t1)
        else
          Branch (p, m, t0, ins t1)
      else
        join (k.tag, Leaf (k,x), p, t)
  in
  ins t

let branch = function
  | (_,_,Empty,t) -> t
  | (_,_,t,Empty) -> t
  | (p,m,t0,t1)   -> Branch (p,m,t0,t1)

let get_prefix = function
  | Empty -> assert false
  | Leaf (k,_) -> k.tag
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
    | Leaf (j,_) as t -> if k.tag == j.tag then Empty else t
    | Branch (p,m,t0,t1) as t ->
      if match_prefix k.tag p m then
        if zero_bit k.tag m then
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
      if j.tag == k.tag then begin
        match f j (Some v0) (Some v1) with
        | Some r -> Leaf (j, r)
        | None -> Empty
      end else begin
        match f j (Some v0) None, f k None (Some v1) with
        | None, None -> Empty
        | Some r, None -> Leaf (j, r)
        | None, Some r -> Leaf (k, r)
        | Some r0, Some r1 ->
          join (j.tag, Leaf (j, r0), k.tag, Leaf (k, r1))
      end

    | ((Leaf (k,v) as left), (Branch (p,m,s0,s1) as t)) ->
      if match_prefix k.tag p m then
        if zero_bit k.tag m then
          branch (p, m, go (left, s0), map_right s1)
        else
          branch (p, m, map_right s0, go (left, s1))
      else begin
        match f k (Some v) None with
        | Some r -> join_safe (Leaf (k, r), map_right t)
        | None -> map_right t
      end

    | ((Branch (p,m,s0,s1) as t), (Leaf (k,v) as right)) ->
      if match_prefix k.tag p m then
        if zero_bit k.tag m then
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
  | Leaf (k,v) -> Hashtbl.hash (k.hkey, hv v)
  | Branch (_,_,left,right) -> Hashtbl.hash (hash hv left, hash hv right)

let rec compare cmp left right = match left,right with
  | Empty, Empty -> 0
  | Empty, _ -> 1
  | _, Empty -> -1
  | Leaf (k0,v0), Leaf (k1,v1) -> begin
      match Pervasives.compare k0.tag k1.tag with
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
  | Leaf (k0, v0), Leaf (k1,v1) -> k0.tag == k1.tag && eq v0 v1
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
