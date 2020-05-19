(** Path expressions *)

(** A path expression for a graph [G] is a regular expression over the
   alphabet of the edges of [G], in which every recognized word is a
   finite path in [G] *)
type t

(** An omega path expression for a graph [G] is an omega regular
   expression over the alphabet of the edges of [G], in which every
   recognized omega word is an infinite path in [G] *)
type omega

type 'a open_pathexpr =
  [ `Edge of int * int
  | `Mul of 'a * 'a
  | `Add of 'a * 'a
  | `Star of 'a
  | `Zero
  | `One ]

type ('a,'b) open_omega_pathexpr =
  [ `Omega of 'a
  | `Mul of 'a * 'b
  | `Add of 'b * 'b ]
  
(** An algebra is a structure equiped with operations for interpreting each
    path expression operation.  *)
type 'a algebra = 'a open_pathexpr -> 'a

(** An omega algebra is a structure equiped with operations for
   interpreting each omega path expression operation.  *)
type ('a,'b) omega_algebra = ('a,'b) open_omega_pathexpr -> 'b

(** Memo table for weight homomorphisms *)
type 'a table

(** Memo table for omega weight homomorphisms *)
type ('a,'b) omega_table

(** Context for managing path expressions *)
type context

val pp : Format.formatter -> t -> unit
val pp_omega : Format.formatter -> omega -> unit
val show : t -> string
val show_omega : omega -> string

(** Create a new path expression context, with a given (optional) table size
    for hashconsed path expressions. *)
val mk_context : ?size:int -> unit -> context

val mk_mul : context -> t -> t -> t
val mk_add : context -> t -> t -> t
val mk_zero : context -> t
val mk_one : context -> t
val mk_star : context -> t -> t
val mk_edge : context -> int -> int -> t

val mk_omega : context -> t -> omega
val mk_omega_add : context -> omega -> omega -> omega
val mk_omega_mul : context -> t -> omega -> omega

(** Evaluate a path expression within some other algebra.  Recursive calls
    to [eval] are memoized so that repeated sub-path expressions are
    evaluated only once.  The optional [table] parameter allows calls to be
    memoized over multiple top-level calls. *)
val eval : ?table:('a table) -> 'a algebra -> t -> 'a

(** Create a new memo table *)
val mk_table : ?size:int -> unit -> 'a table

(** Create a new omega memo table *)
val mk_omega_table : ?size:int -> 'a table -> ('a,'b) omega_table

(** Forget memoized values for path expressions that involve edges that do
    not satisfy the given predicate. *)
val forget : 'a table -> (int -> int -> bool) -> unit

(** Evaluate an omega path expression within some other algebra.
   Recursive calls to [eval_omega] are memoized so that repeated
   sub-path expressions are evaluated only once.  The optional [table]
   parameter allows calls to be memoized over multiple top-level
   calls. *)
val eval_omega : ?table:(('a,'b) omega_table) ->
                 'a algebra ->
                 ('a,'b) omega_algebra ->
                 omega ->
                 'b

(** Check whether two path expressions recognize the same language *)
val equiv : context -> t -> t -> bool
