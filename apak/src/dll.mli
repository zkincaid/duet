(** Imperative doubly-linked lists *)
type 'a dll_node
type 'a t

val create : unit -> 'a t

val size : 'a t -> int
val is_empty : 'a t -> bool
val top : 'a t -> 'a
val iter : ('a -> unit) -> 'a t -> unit
val elt : 'a dll_node -> 'a

(** Destructive concatenation.  Neither [a] nor [b] is safe to use after
    calling [concat a b] *)
val concat : 'a t -> 'a t -> 'a t
val push : 'a -> 'a t -> 'a dll_node
val delete : 'a t -> 'a dll_node -> unit
