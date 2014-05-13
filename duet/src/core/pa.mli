(** Common operations for pointer analyses *)

open Core
open Apak

(** {2 Core pointer analysis types and operations} *)

(** Types for representing memory and pointer analyses *)

(** [membase] represents a chunk of memory, which may reside on the stack or on
    the heap. *)
type membase =
  | MAddr of varinfo
  | MStr of string
  | MAlloc of def
  | MTmp of int (** Temporary memory location - does not correspond to anything
		    in the program *)

(** A memory location consists of a base and an offset.  The location of
    (base,offset) is base+offset if offset is fixed, and some nondeterministic
    location {i within the chunk of memory allocated at base} if offset is
    OffsetUnknown. *)
type memloc = membase * offset

module MemBase : Putil.CoreType with type t = membase
module MemLoc : sig
  include Putil.CoreType with type t = memloc
  val is_shared : t -> bool
  val is_var : t -> bool
end

(** Common pointer analysis operations *)
class virtual ptr_anal : CfgIr.file -> object

  (** Possible points-to targets of an access path *)
  method virtual ap_points_to : ap -> MemLoc.Set.t

  (** Possible points-to targets of an expression  *)
  method virtual expr_points_to : expr -> MemLoc.Set.t

  (** Determine whether two access paths may be aliased (as lvalues). *)
  method may_alias : ap -> ap -> bool

  (** Possible locations that an {b lvalue} could refer to (in contrast to
      ap_points_to, which determines the possible locations that an {b rvalue}
      could refer to)  *)
  method resolve_ap : ap -> MemLoc.Set.t

  (** Possible targets of a function call expression.  This is really just the
      variable locations an expression could evaluate to.  [resolve_call] does
      not guarantee that the variables returned are function typed. *)
  method resolve_call : expr -> Varinfo.Set.t

  (** Check whether a function call may have an undefined target (a function
      without available source code). *)
  method has_undefined_target : expr -> bool
end

(** {2 Simplification} *)

(** Simplification operations for access paths and expressions that are useful
    for generating pointer analysis constraints. *)

(** Simplified access path.  A level-0 access path accesses the heap 0 times,
    and a level-1 access path accesses the heap once.  [Lvl0(v,of)] represents
    the access path [v.of], and [Lvl1(v,of1,of2)] represents the access path
    [[*(v.of1)].of2] *)
type simple_ap =
  | Lvl0 of Var.t          (** [Lvl0 (v,of)] ~ [v.of] *)
  | Lvl1 of Var.t * offset (** [Lvl1 (v,of,of2)] ~ [[*(v.of1)].of2] *)

(** [rhsbase] represents an expression that addresses a chunk of memory (or
    could possible address a chunk of memory). *)
type rhsbase =
  | RAp of simple_ap
  | RAddr of varinfo
  | RStr of string

(** A [simple_rhs] is a representation of an expression that evaluates to a
    memory location.  It consists of a [rhsbase] which evaluates to a chunk of
    memory, and an offset within that chunk. *)
type simple_rhs = rhsbase * offset

module SimpleAP : sig
  include Putil.Ordered with type t = simple_ap
  module Set : Putil.Set.S with type elt = simple_ap
end
module SimpleRhs : sig
  include Putil.Ordered with type t = simple_rhs
  module Set : Putil.Set.S with type elt = simple_rhs
end

(** A [value] extends an expression value type with a constant integer case.
    It is used to simplify expressions by folding constants. *)
type 'a value =
  | VConst of int
  | VRhs of 'a

(** Rhs represents a domain suitable for the interpretation of pointer
    expressions. MakeEval defines an evaluation function that lifts the
    interpretation of primitive operations in Rhs to an interpretation of
    integer/pointer expressions. *)
module MakeEval : functor (Rhs : sig
		  type t
		  val str_const : string -> t
		  val addr_of : Var.t -> t
		  val havoc : t
		  val change_offset : (int -> offset) -> t -> t
		  val join : t -> t -> t
		end) ->
sig
  val eval : expr -> (ap -> Rhs.t) -> Rhs.t value
end


exception Higher_ap of SimpleRhs.t

val simplify_ap : ap -> SimpleAP.Set.t
val simplify_expr : expr -> SimpleRhs.Set.t value

(** {2 Default pointer analysis operations} *)

(** Various operations on a default pointer analysis implementation (which
    must be set using [set_pa] before using).  See the documentation of
    {!ptr_anal} for descriptions of these functions.  *)

(** Set the default pointer analysis.  This must be called before any of the
    default operations below *)
val set_pa : ptr_anal -> unit
val set_init : (CfgIr.file -> ptr_anal) -> unit

val ap_points_to : ap -> MemLoc.Set.t
val expr_points_to : expr -> MemLoc.Set.t
val may_alias : ap -> ap -> bool
val resolve_ap : ap -> MemLoc.Set.t
val resolve_call : expr -> Varinfo.Set.t
val has_undefined_target : expr -> bool
(*val ap_is_shared : ap -> bool*)

(** Simplify function calls by passing parameters and return variables through
    global variables.  So, for example, [r = foo(exp1,exp2)] becomes

{[param0 = exp1
param1 = exp2
foo()
r = return v]}
*)
val simplify_calls : CfgIr.file -> unit
