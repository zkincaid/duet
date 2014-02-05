(*pp camlp4find deriving.syntax *)

open BatPervasives

type ('a, 'b) typ =
| Atom of 'a
| Block of 'b

module type Vertex = sig
  include Putil.CoreType
  type atom
  type block
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

module Make (V : Vertex) (Block : BLOCK with type t = V.block) =
struct
  module GI = ExtGraph.Persistent.Digraph.Make(V)
  module G = struct
    include GI
    include ExtGraph.Build.Make(GI)
  end

  module M = BatMap.Make(Block)
  module Block = Block

  type atom = V.atom
  type block = V.block
  type vertex = V.t
  type edge = G.E.t

  type block_def =
    { bentry : V.t;
      bexit : V.t;
      bbody : G.t }

  type t = block_def M.t

  let classify = V.classify

  let block_entry rg block = (M.find block rg).bentry
  let block_exit rg block = (M.find block rg).bexit
  let block_body rg block = (M.find block rg).bbody
(*  let block_body rg block = try (M.find block rg).bbody with Not_found -> failwith ("Couldn't find block " ^ (Block.show block))*)
  let blocks = M.keys
  let bodies rg = M.enum rg /@ (fun (block, def) -> (block, def.bbody))
  let vertices rg =
    let f (block, def) = (G.vertices def.bbody) /@ (fun v -> (block, v)) in
    BatEnum.concat (BatEnum.map f (M.enum rg))

  let map f rg =
    let g block def = { def with bbody = f block def.bbody } in
    M.mapi g rg

  let empty = M.empty
  let add_block rg block body ~entry:en ~exit:ex =
    let def = { bentry = en; bexit = ex; bbody = body } in
    M.add block def rg
  let remove_block rg block = M.remove block rg
  let mem rg block = M.mem block rg
  let find_block rg p = BatEnum.find p (blocks rg)
end

module Callgraph(R : S) = struct
  module CG = ExtGraph.Persistent.Digraph.Make(R.Block)
  module U = ExtGraph.Unfold.Make(CG)
  include CG
  let callgraph rg root =
    let succ block =
      let f v = match R.classify v with
	| Atom _  -> None
	| Block b -> Some b
      in
      BatEnum.filter_map f (R.G.vertices (R.block_body rg block))
    in
    U.unfold root succ
end
