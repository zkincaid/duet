open Core

val whole_program : bool ref

module Cfg : sig
  include Afg.FlowGraph with type V.t = Def.t
			and type E.label = unit
  val initial_vertex : t -> Def.t
  val display : t -> unit
  val sanity_check : t -> unit
  val reverse_postorder : t -> (V.t -> V.t -> int)
  val clone : t -> t
end

module CfgBuilder : sig
  type ivl = Def.t * Def.t
  val mk_skip : Cfg.t -> ivl
  val mk_single : Cfg.t -> Def.t -> ivl
  val mk_seq : Cfg.t -> ivl -> ivl -> ivl
  val mk_block : Cfg.t -> ivl list -> ivl
  val mk_if : Cfg.t -> Bexpr.t -> ivl -> ivl -> ivl
end

type func = {
  mutable fname : varinfo;
  mutable formals: varinfo list;
  mutable locals: varinfo list;
  mutable cfg: Cfg.t;
  mutable file: file option;
}
and file = {
  mutable filename : string;
  mutable funcs : func list;
  mutable threads : varinfo list;
  mutable entry_points : varinfo list;
  mutable vars : varinfo list;
  mutable types : typ list; (** named types *)
  mutable globinit : func option;
}

val mk_local_varinfo : func -> string -> typ -> Varinfo.t
val mk_global_varinfo : file -> string -> typ -> Varinfo.t
val mk_thread_local_varinfo : file -> string -> typ -> Varinfo.t

val mk_local_var : func -> string -> typ -> Var.t
val mk_global_var : file -> string -> typ -> Var.t
val mk_thread_local_var : file -> string -> typ -> Var.t

val gfile : file option ref
val get_gfile : unit -> file

val defined_function : Varinfo.t -> file -> bool
val lookup_function : Varinfo.t -> file -> func
val lookup_function_name : string -> file -> func

val insert_pre : Def.t -> Def.t -> Cfg.t -> unit
val insert_succ : Def.t -> Def.t -> Cfg.t -> unit

val from_file_ast : Ast.file -> file

val cfg_equal : Cfg.t -> Cfg.t -> bool

val return_var : Varinfo.t -> Varinfo.t

val is_local : func -> Varinfo.t -> bool
val is_formal : func -> Varinfo.t -> bool

val iter_func_defs : (Varinfo.t -> Def.t -> unit) -> file -> unit
val iter_defs : (Def.t -> unit) -> file -> unit

val remove_unreachable : Cfg.t -> Def.t -> unit

(** Normalize a file.  This should be called immediately after constructing a
    file.  Normalization ensures that:
    - CFGs are well-formed:
      + There is a single entry vertex (with no predecessors)
      + There is a single exit vertex (with no successors)
      + Every vertex is reachable from the entry vertex
    - String constants do not appear as the RHS of a store

    Normalization also inserts skip vertices in places that are structurally
    convenient for SESE region detection.
*)
val normalize : file -> unit
