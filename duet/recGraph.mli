(** Recursive graphs *)

type (+'a, +'b) seq_typ = [ `Atom of 'a | `Block of 'b ]
type (+'a, +'b) par_typ = [ ('a, 'b) seq_typ | `ParBlock of 'b ]

module type Vertex = sig
  include Putil.CoreType
  type atom
  type block
  type ('a, 'b) typ
  val classify : t -> (atom, block) typ
end
module type BLOCK = Putil.CoreType

module type S = sig

  module Block : BLOCK
  module G : sig
    include ExtGraph.P
    val split : t -> vertex -> pred:vertex -> succ:vertex -> t
    val eliminate_vertex : t -> vertex -> t
  end

  type t
  type atom
  type block = Block.t
  type ('a, 'b) typ

  val classify : G.V.t -> (atom, block) typ
  val block_entry : t -> block -> G.V.t
  val block_exit : t -> block -> G.V.t
  val block_body : t -> block -> G.t
  val blocks : t -> block BatEnum.t
  val bodies : t -> (block * G.t) BatEnum.t
  val vertices : t -> (block * G.V.t) BatEnum.t
  val mem : t -> block -> bool

  val map : (block -> G.t -> G.t) -> t -> t
  val empty : t
  val add_block : t -> block -> G.t -> entry:G.V.t -> exit:G.V.t -> t
  val remove_block : t -> block -> t
  val find_block : t -> (block -> bool) -> block
end

module Make (V : Vertex) (Block : BLOCK with type t = V.block) :
  S with type G.V.t = V.t
     and type Block.t = V.block
     and type atom = V.atom
     and type ('a, 'b) typ = ('a, 'b) V.typ

module Callgraph (R : S with type ('a, 'b) typ = ('a, 'b) par_typ) :
sig
  include ExtGraph.P with type V.t = R.Block.t
  val callgraph : R.t -> R.Block.t -> t
end

module LiftPar(R : S with type ('a, 'b) typ = ('a, 'b) seq_typ) :
  S with type ('a, 'b) typ = ('a, 'b) par_typ
     and module Block = R.Block
     and module G = R.G
     and type t = R.t
     and type atom = R.atom
     and type block = R.block
