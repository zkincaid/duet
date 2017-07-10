open Pervasives
open BatPervasives

module type Vertex = sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end

(* BiPartite Graph Matching *)
module type S = sig
  type t
  type vertex

  val pp : Format.formatter -> t -> unit

  (* An Empty BiPartite Graph *)
  val empty : t

  (* Makes a BiPartite Graph given Vertices U,V and edges E*)
  val make : vertex BatEnum.t -> vertex BatEnum.t -> (vertex * vertex) BatEnum.t -> t

  (* Returns cardinality of Maximum Matching on Graph *)
  val max_matching : t -> int

  (* Returns cardinality of U *)
  val u_size : t -> int

  (* Returns cardinality of V *)
  val v_size : t -> int

  (* Returns number of vertices in U incident to an edge *)
  val incident_u : t -> int

  (* Returns number of vertices in V incident to an edge *)
  val incident_v : t -> int
end

module Make (V : Vertex) : S with type vertex = V.t
