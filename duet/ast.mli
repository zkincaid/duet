open Core
(** Statement kind *)
type stmt_kind =
  | Branch        of stmt * stmt
  | Instr         of def list
  | Goto          of int (** Statement id *)
  | ForkGoto      of int (** Statement id *)
  | Block         of stmt list
and stmt = {
  sid : int; (** Statement id *)
  mutable skind : stmt_kind;
}

(** Function definition type *)
type funcdec = {
  mutable fname : varinfo;
  mutable formals : varinfo list;
  mutable locals : varinfo list;
  mutable body : stmt list;
  mutable file : file option;
}
and file = {
  mutable filename : string;
  mutable funcs : funcdec list;
  mutable vars : varinfo list;
  mutable globinit : funcdec option;
  mutable max_sid : int;
  mutable types : typ list; (** named types *)
  mutable stmt_map : (int,stmt) Hashtbl.t
}

type 'a open_stmt =
  | OBranch        of 'a * 'a
  | OInstr         of def list
  | OGoto          of int
  | OForkGoto      of int
  | OBlock         of 'a list

val mk_file : string -> file
val mk_stmt : file -> stmt_kind -> stmt
val stmt_kind : stmt -> stmt_kind
val pp_stmt : Format.formatter -> stmt -> unit
val lookup_stmt : file -> int -> stmt
val stmt_id : stmt -> int

val fold_stmt : ('a open_stmt -> 'a) -> stmt -> 'a

val iter_defs_stmt : (def -> unit) -> stmt -> unit
val iter_defs_file : (def -> unit) -> file -> unit

module StmtHT : Hashtbl.S with type key = stmt
module StmtSet : Set.S with type elt = stmt
module StmtCfg : Graph.Sig.I with type V.t = stmt

val construct_cfg : file -> funcdec -> StmtCfg.t
