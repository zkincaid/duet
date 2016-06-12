(** Core contains the core type definitions and conversion functions used by
    our internal representations, including the type [ap] of access paths and
    [expr] of expressions. *)

open Apak

(** {2 Core types} *)

(** Record containing the information of enumeration (in C), use java
    class for java enumerations *)
type enuminfo = {
  enname : string;
  mutable enitems : (string * int) list
}

(** Concrete type (any type that is not a named type *)
type ctyp =
  | Void
  | Lock
  | Int       of int
  | Float     of int
  | Pointer   of typ
  | Array     of typ * int option 
  | Record    of recordinfo
  | Enum      of enuminfo
  | Func      of typ * typ list (** A function type consists of a return type
                                    and a list of parameter types. *)
  | Union     of recordinfo
  | Dynamic (** A default type for values that cannot be assigned a static
                type, or whose static type is misleading or uninformative *)
and typ =
  | Named     of string * ctyp ref (** A named type consists of a name and a
                                       reference to its underlying concrete
                                       type *)
  | Concrete  of ctyp

and field = {
  finame : string;
  fityp : typ;
  fioffset : int;
}

and recordinfo = {
  rname : string;
  rfields : field list;
  rkey : int; (* key required for duplicate structs etc.*)
}

(** Unary operations *)
type unop =
  | Neg
  | BNot

(** Binary operations *)
type binop =
  | Add
  | Minus
  | Mult
  | Div 
  | Mod 
  | ShiftL
  | ShiftR
  | BXor
  | BAnd
  | BOr

(** Predicates *)
type pred =
  | Lt
  | Le
  | Eq
  | Ne

type visibility =
  | VzGlobal      (** Global variable *)
  | VzLocal       (** Local variable *)
  | VzThreadLocal (** Thread local variable (per-thread variable with global
                      scope) *)
type varinfo deriving (Show,Compare)
type offset =
  | OffsetFixed of int
  | OffsetUnknown
      deriving (Compare)
type var = varinfo * offset deriving (Show)

(** Constants. *)
type constant =
  | CInt    of int * int (** CInt(i,w) represents constant i of width w *)
  | CString of string
  | CChar   of char
  | CFloat  of float * int (** CFloat(f,w) represents constant f of width w *)

(** Access paths *)
type ap =
  | Variable      of var
  | Deref         of expr

(** Boolean expressions (in negation normal form) *)
and bexpr =
  | Atom          of (pred * expr * expr)
  | And           of (bexpr * bexpr)
  | Or            of (bexpr * bexpr)

(** Expressions *)
and expr =
  | Havoc         of typ
  | Constant      of constant
  | Cast          of typ * expr
  | BinaryOp      of expr * binop * expr * typ
  | UnaryOp       of unop * expr * typ
  | AccessPath    of ap
  | BoolExpr      of bexpr
  | AddrOf        of ap (** It is not generally safe to use this
                            constructor; use [addr_of] instead *)
        deriving (Show,Compare)

type alloc_target =
  | AllocHeap
  | AllocStack

(** Builtin definitions *)
type builtin =
  | Alloc of (var * expr * alloc_target)
  | Free of expr
  | Fork of (var option * expr * expr list)
  | Acquire of expr
  | Release of expr
  | AtomicBegin
  | AtomicEnd
  | Exit

(** Definition kind *)
and defkind =
  | Assign of (var * expr)
  | Store of (ap * expr)
  | Call of (var option * expr * expr list)
  | Assume of bexpr
  | Initial
  | Assert of bexpr * string
  | AssertMemSafe of expr * string
  | Return of expr option
  | Builtin of builtin

and def =
  { did : int;
    mutable dkind : defkind }

module Varinfo: sig
  include Putil.CoreType with type t = varinfo

  (** Determine the type of a varinfo.  This type should not be relied on. *)
  val get_type : t -> typ

  val mk_global : string -> typ -> t
  val mk_local : string -> typ -> t
  val mk_thread_local : string -> typ -> t

  val clone : varinfo -> t
  val get_visibility : t -> visibility
  val is_global : t -> bool
  val is_shared : t -> bool
  val addr_taken : t -> bool
  val set_global : t -> unit
  val subscript : t -> int -> varinfo
  val get_subscript : t -> int
end

module Var : sig
  include Putil.CoreType with type t = var
  val get_type : t -> typ
  val get_visibility : t -> visibility
  val is_global : t -> bool
  val is_shared : t -> bool
  val subscript : var -> int -> var
  val unsubscript : var -> var
  val get_subscript : var -> int
  val mk : varinfo -> var
  val get_id : t -> int
end

module Offset : sig
  include Putil.CoreType with type t = offset
  val add : t -> t -> t
end

(** {b Deriving instances for core types} *)

module Compare_def : Deriving_Compare.Compare with type a = def

(** {2 Core operations} *)

val is_pointer_type : typ -> bool
val is_numeric_type : typ -> bool
val typ_equiv : typ -> typ -> bool
val typ_width : typ -> int

val typ_string : typ
val char_width : int
val bool_width : int
val machine_int_width : int
val pointer_width : int
val unknown_width : int

(** Return the underyling concrete type of a (possibly named) type *)
val resolve_type : typ -> ctyp

val format_typ : Format.formatter -> typ -> unit

val get_offsets : varinfo -> Var.Set.t

val eval_binop : binop -> int -> int -> int

(** {2 Expression folding } *)

type ('a, 'b, 'c) open_expr =
  | OHavoc         of typ
  | OConstant      of constant
  | OCast          of typ * 'a
  | OBinaryOp      of 'a * binop * 'a * typ
  | OUnaryOp       of unop * 'a * typ
  | OAccessPath    of 'c
  | OBoolExpr      of 'b
  | OAddrOf        of 'c
type ('a, 'b) open_bexpr =
  | OAtom of (pred * 'a * 'a)
  | OAnd of ('b * 'b)
  | OOr of ('b * 'b)

type ('a, 'b, 'c) expr_algebra = ('a, 'b, 'c) open_expr -> 'a
type ('a, 'b) bexpr_algebra = ('a, 'b) open_bexpr -> 'b

(** {2 Access paths } *)
module AP : sig
  include Putil.CoreType with type t = ap
  val get_type : t -> typ
  val get_ctype : t -> ctyp
  val get_visibility : t -> visibility
  val is_global : t -> bool
  val is_shared : t -> bool
  val subscript : int -> ap -> ap
  val unsubscript : ap -> ap

  val accessed : t -> Set.t
  val free_vars : t -> Var.Set.t
  val subst_expr : (expr -> expr) -> t -> t
  val subst_ap : (ap -> ap) -> t -> t
  val subst_var : (var -> var) -> t -> t
  val psubst_var : (var -> var option) -> t -> t option
  val strip_all_casts : t -> t
  val offset : t -> offset -> t
end

(** {2 Expressions } *)
module Expr : sig
  include Putil.CoreType with type t = expr

  val const_int : int -> t
  val one : t
  val zero : t
  val null : typ -> t
  val add : t -> t -> t
  val sub : t -> t -> t
  val mul : t -> t -> t
  val div : t -> t -> t
  val modulo : t -> t -> t
  val neg : t -> t

  (** Take the address of an access path.  This should always be used instead
      of the AddrOf constructor *)
  val addr_of : ap -> t

  val get_uses : t -> AP.Set.t
  val accessed : t -> AP.Set.t
  val free_vars : t -> Var.Set.t
  val subst_expr : (expr -> expr) -> t -> t
  val subst_ap : (ap -> ap) -> t -> t
  val subst_var : (var -> var) -> t -> t
  val psubst_var : (var -> var option) -> t -> t option
  val simplify : t -> t

  (** Remove all leading casts from an expression (lower-level sub-expressions
      may still contain casts) *)
  val strip_casts : t -> t

  (** Remove all casts from an expression. *)
  val strip_all_casts : t -> t

  (** Determine the type of an expression.  This type should not be relied
      on. *)
  val get_type : t -> typ

  val fold : ('a, bexpr, ap) expr_algebra -> t -> 'a
  val deep_fold : ('a, 'b, ap) expr_algebra -> ('a, 'b) bexpr_algebra
    -> t -> 'a
end

(** {2 Boolean expressions } *)
module Bexpr : sig 
  include Putil.CoreType with type t = bexpr
  val negate : t -> t
  val implies : t -> t -> t
  val gt : expr -> expr -> t
  val ge : expr -> expr -> t
  val ktrue : t
  val kfalse : t
  val havoc : t
  val of_expr : expr -> t

  val get_uses : t -> AP.Set.t
  val accessed : t -> AP.Set.t
  val free_vars : t -> Var.Set.t
  val subst_expr : (expr -> expr) -> t -> t
  val subst_ap : (ap -> ap) -> t -> t
  val subst_var : (var -> var) -> t -> t
  val psubst_var : (var -> var option) -> t -> t option

  val eval : t -> bool option
  val dnf : t -> t
  val simplify : t -> t
  val strip_all_casts : t -> t

  val fold : (expr, 'b) bexpr_algebra -> t -> 'b
  val deep_fold : ('a, 'b, ap) expr_algebra -> ('a, 'b) bexpr_algebra
    -> t -> 'b
end

(** {2 Definitions } *)
module Def : sig 
  include Putil.CoreType with type t = def
  val get_defs : t -> AP.Set.t
  val get_uses : t -> AP.Set.t
  val get_accessed : t -> AP.Set.t
  val free_vars : t -> Var.Set.t
  val assigned_var : t -> var option
  val initial : t
  val clone : t -> t
  val mk : ?loc:Cil.location -> defkind -> t
  val get_location : t -> Cil.location
end
