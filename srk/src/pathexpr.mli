type t

type 'a open_pathexpr =
  [ `Edge of int * int
  | `Mul of 'a * 'a
  | `Add of 'a * 'a
  | `Star of 'a
  | `Zero
  | `One ]

(** An algebra is a structure equiped with operations for interpreting each
    path expression operation.  *)
type 'a algebra = 'a open_pathexpr -> 'a

(** Memo table for weight homomorphisms *)
type 'a table

(** Context for managing path expressions *)
type context

val pp : Format.formatter -> t -> unit

(** Create a new path expression context, with a given (optional) table size
    for hashconsed path expressions. *)
val mk_context : ?size:int -> unit -> context

val mk_mul : context -> t -> t -> t
val mk_add : context -> t -> t -> t
val mk_zero : context -> t
val mk_one : context -> t
val mk_star : context -> t -> t
val mk_edge : context -> int -> int -> t

(** Evaluate a path expression within some other algebra.  Recursive calls
    to [eval] are memoized so that repeated sub-path expressions are
    evaluated only once.  The optional [table] parameter allows calls to be
    memoized over multiple top-level calls. *)
val eval : ?table:('a table) -> ('a open_pathexpr -> 'a) -> t -> 'a

(** Create a new memo table *)
val mk_table : ?size:int -> unit -> 'a table

(** Forget memoized values for path expressions that involve edges that do
    not satisfy the given predicate. *)
val forget : 'a table -> (int -> int -> bool) -> unit
