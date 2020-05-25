(** {1 Path expressions} *)

type simple
type nested

(** A simple path expression for a graph [G] is a regular expression
   over the alphabet of the edges of [G], in which every recognized
   word is a finite path in [G].  A nested path expression is a simple
   path expression extended with a Segment operator, which is used to
   group sub-expressions; nested path expressions recognize nested
   paths, which are paths equipped with nested grouping structure. *)
type 'a t

(** Context for managing path expressions *)
type context

val pp : Format.formatter -> 'a t -> unit
val show : 'a t -> string

(** Create a new path expression context, with a given (optional) table size
    for hashconsed path expressions. *)
val mk_context : ?size:int -> unit -> context

(** Check whether two path expressions recognize the same language *)
val equiv : context -> simple t -> simple t -> bool

(** {2 Constructors} *)

val mk_mul : context -> 'a t -> 'a t -> 'a t
val mk_add : context -> 'a t -> 'a t -> 'a t
val mk_zero : context -> 'a t
val mk_one : context -> 'a t
val mk_star : context -> 'a t -> 'a t
val mk_edge : context -> int -> int -> 'a t

val mk_segment : context -> 'a t -> nested t

(** Cast a simple path expression to a nested path expression. *)
val promote : simple t -> nested t

(** {2 Evaluation} *)

type 'a open_pathexpr =
  [ `Edge of int * int
  | `Mul of 'a * 'a
  | `Add of 'a * 'a
  | `Star of 'a
  | `Zero
  | `One ]

type 'a open_nested_pathexpr =
  [ `Segment of 'a
  | 'a open_pathexpr ]
  
(** An algebra is a structure equiped with operations for interpreting each
    path expression operation.  *)
type 'a algebra = 'a open_pathexpr -> 'a

(** An nested algebra is a structure equiped with operations for
   interpreting each nested path expression operation.  *)
type 'a nested_algebra = 'a open_nested_pathexpr -> 'a

(** Memo table for weight homomorphisms *)
type 'a table

(** Create a new memo table *)
val mk_table : ?size:int -> unit -> 'a table

(** Evaluate a path expression within some other algebra.  Recursive calls
    to [eval] are memoized so that repeated sub-path expressions are
    evaluated only once.  The optional [table] parameter allows calls to be
    memoized over multiple top-level calls. *)
val eval : ?table:('a table) ->
           algebra:([>'a open_pathexpr] -> 'a) ->
           simple t ->
           'a

val eval_nested : ?table:('a table) ->
                  algebra:([>'a open_nested_pathexpr] -> 'a) ->
                  nested t ->
                  'a

(** Forget memoized values for path expressions that involve edges that do
    not satisfy the given predicate. *)
val forget : 'a table -> (int -> int -> bool) -> unit

(** {1 Omega path expressions} *)

(** An omega path expression for a graph [G] is an omega regular
   expression over the alphabet of the edges of [G], in which every
   recognized omega word is an infinite path in [G] *)
type 'a omega

val pp_omega : Format.formatter -> 'a omega -> unit
val show_omega : 'a omega -> string

(** {2 Constructors} *)

val mk_omega : context -> 'a t -> 'a omega
val mk_omega_add : context -> 'a omega -> 'a omega -> 'a omega
val mk_omega_mul : context -> 'a t -> 'a omega -> 'a omega

(** Cast a simple omega path expression to a nested omega path
   expression. *)
val promote_omega : simple omega -> nested omega

(** {2 Evaluation} *)

type ('a,'b) open_omega_pathexpr =
  [ `Omega of 'a
  | `Mul of 'a * 'b
  | `Add of 'b * 'b ]

(** An omega algebra is a structure equiped with operations for
   interpreting each omega path expression operation.  *)
type ('a,'b) omega_algebra = ('a,'b) open_omega_pathexpr -> 'b

(** Memo table for omega weight homomorphisms *)
type ('a,'b) omega_table

(** Create a new omega memo table *)
val mk_omega_table : ?size:int -> 'a table -> ('a,'b) omega_table

(** Evaluate an omega path expression within some other algebra.
   Recursive calls to [eval_omega] are memoized so that repeated
   sub-path expressions are evaluated only once.  The optional [table]
   parameter allows calls to be memoized over multiple top-level
   calls. *)
val eval_omega : ?table:(('a,'b) omega_table) ->
                 algebra:('a nested_algebra) ->
                 omega_algebra:(('a,'b) omega_algebra) ->
                 nested omega ->
                 'b
