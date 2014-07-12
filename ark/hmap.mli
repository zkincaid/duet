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

(*i $Id: hmap.mli,v 1.5 2008-07-21 14:53:06 filliatr Exp $ i*)

(*s Maps over hash-consed values, implemented as Patricia trees.
    See the module [Hashcons] and [Ptmap]. *)

type ('a, 'b) t

type 'a key = 'a Hashcons.hash_consed

val empty : ('a, 'b) t

val add : 'a key -> 'b -> ('a, 'b) t -> ('a, 'b) t

val find : 'a key -> ('a, 'b) t -> 'b

val remove : 'a key -> ('a, 'b) t -> ('a, 'b) t

val mem :  'a key -> ('a, 'b) t -> bool

val iter : ('a key -> 'b -> unit) -> ('a, 'b) t -> unit

val map : ('b -> 'c) -> ('a, 'b) t -> ('a, 'c) t

val mapi : ('a key -> 'b -> 'c) -> ('a, 'b) t -> ('a, 'c) t

val fold : ('a key -> 'b -> 'c -> 'c) -> ('a, 'b) t -> 'c -> 'c

val enum : ('a, 'b) t -> ('a key * 'b) BatEnum.t

val of_enum : ('a key * 'b) BatEnum.t -> ('a, 'b) t

val filterv : ('b -> bool) -> ('a, 'b) t -> ('a, 'b) t

val filter : ('a key -> 'b -> bool) -> ('a, 'b) t -> ('a, 'b) t

val filter_map : ('a key -> 'b -> 'c option) -> ('a, 'b) t -> ('a, 'c) t

val merge : ('a key -> 'b option -> 'c option -> 'd option) ->
       ('a, 'b) t -> ('a, 'c) t -> ('a, 'd) t

val hash : ('b -> int) -> ('a, 'b) t -> int

val compare : ('b -> 'b -> int) -> ('a, 'b) t -> ('a, 'b) t -> int

val equal : ('b -> 'b -> bool) -> ('a, 'b) t -> ('a, 'b) t -> bool

val min_binding : ('a, 'b) t -> ('a key * 'b)
val max_binding : ('a, 'b) t -> ('a key * 'b)
