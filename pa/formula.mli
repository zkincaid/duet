type 'a term =
  | Var of int
  | Const of 'a

type ('a,'b) formula

type ('a,'b,'c) open_formula = [
  | `T
  | `F
  | `And of 'c * 'c
  | `Or of 'c * 'c
  | `Atom of 'a * ('b term) list
  | `Forall of (string option) * 'c
  | `Exists of (string option) * 'c
  | `Eq of ('b term) * ('b term)
  | `Neq of ('b term) * ('b term)
]

val destruct : ('a, 'b) formula -> ('a, 'b, ('a,'b) formula) open_formula
val destruct_flatten : ('a, 'b) formula -> [
  | `T
  | `F
  | `And of (('a,'b) formula list)
  | `Or of (('a,'b) formula list)
  | `Atom of 'a * ('b term) list
  | `Forall of (string option list) * ('a,'b) formula
  | `Exists of (string option list) * ('a,'b) formula
  | `Eq of ('b term) * ('b term)
  | `Neq of ('b term) * ('b term)
  ]
val construct : ('a, 'b, ('a,'b) formula) open_formula -> ('a, 'b) formula

val eval : (('a, 'b, 'c) open_formula -> 'c) -> ('a, 'b) formula -> 'c

(** Apply a substitution on constants *)
val substitute : ('b -> 'c term) -> ('a, 'b) formula -> ('a, 'c) formula

(** Apply a substitution on *free* variables *)
val var_substitute : (int -> 'b term) -> ('a, 'b) formula -> ('a, 'b) formula

(** Atom substitution *)
val atom_substitute : ('a -> int -> ('c, 'b) formula) -> ('a, 'b) formula ->
  ('c, 'b) formula

val pp : (Format.formatter -> 'a -> unit) ->
  (Format.formatter -> 'b -> unit) ->
  Format.formatter ->
  ('a,'b) formula ->
  unit

val tptp3_pp : (Format.formatter -> 'a -> unit) ->
  (Format.formatter -> 'b -> unit) ->
  Format.formatter ->
  ('a,'b) formula ->
  unit

val smtlib2_pp : (Format.formatter -> 'a -> unit) ->
  (Format.formatter -> 'b -> unit) ->
  Format.formatter ->
  ('a,'b) formula ->
  unit

val mk_false : ('a,'b) formula
val mk_true : ('a,'b) formula
val mk_and : ('a,'b) formula -> ('a,'b) formula -> ('a,'b) formula
val mk_or : ('a,'b) formula -> ('a,'b) formula -> ('a,'b) formula
val mk_eq : ('b term) -> ('b term) -> ('a, 'b) formula
val mk_neq : ('b term) -> ('b term) -> ('a, 'b) formula
val mk_atom : 'a -> ('b term) list -> ('a, 'b) formula
val mk_exists : ?name:(string option) -> ?var:int ->
  ('a, 'b) formula -> ('a, 'b) formula
val mk_forall : ?name:(string option) -> ?var:int ->
  ('a, 'b) formula -> ('a, 'b) formula
val const_exists : ?equal:('b -> 'b -> bool) -> ?name:(string option) ->
  'b -> ('a,'b) formula -> ('a,'b) formula
val const_forall : ?equal:('b -> 'b -> bool) -> ?name:(string option) ->
  'b -> ('a,'b) formula -> ('a,'b) formula

val big_conj : ('a,'b) formula BatEnum.t -> ('a, 'b) formula
val big_disj : ('a,'b) formula BatEnum.t -> ('a, 'b) formula

(** Alpha equivalence *)
val alpha_equiv : ('a,'b) formula -> ('a,'b) formula -> bool

val instantiate_quantifiers : ?env:('b list) ->
  ('a,'b) formula -> 'b list -> ('a,'b) formula

val simplify : ('a,'b) formula -> ('a,'b) formula

val alpha_of_int : int -> string
