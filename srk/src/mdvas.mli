(** Wedge abstract domain.  A wedge corresponds to a conjunction of equations
    and inequations over a vocabulary that includes addition, multiplication,
    exponentiation, logarithm, division, and modulo. *)
open Syntax
module V = Linear.QQVector
module M = Linear.QQMatrix
module Z = Linear.ZZVector
type transformer =
  { a : Z.t;
    b : V.t }
[@@deriving ord, show]


module TSet : BatSet.S with type elt = transformer

type vas = TSet.t

type 'a t = { v : vas; s_lst : M.t list; invars : 'a formula list; guarded_system : bool}

val gamma : 'a context ->  'a t -> (symbol * symbol) list -> 'a formula

val abstract : ?exists:(symbol -> bool) -> 
  'a context ->
  (symbol * symbol) list -> 
  'a formula ->
  'a t

val pp : 'a context -> (symbol * symbol) list -> Format.formatter -> 'a t -> unit

val exp : 'a context -> (symbol * symbol) list -> 'a term -> 'a t -> 'a formula

val join : 'a context -> (symbol * symbol) list -> 'a t -> 'a t -> 'a t
val widen : 'a context -> (symbol * symbol) list -> 'a t -> 'a t -> 'a t
val equal : 'a context -> (symbol * symbol) list -> 'a t -> 'a t -> bool
val postify : 'a context -> (symbol * symbol) list -> 'a formula -> 'a formula
val exp_base_helper : 'a context -> (symbol * Symbol.Map.key) list -> 'a term ->
  M.t list -> transformer list -> 
  'a formula * (('a term list * (('a, 'b) expr * Z.dim) list * ('a, 'c) expr * ('a, 'd) expr)
                  list * 'a term list list * ('a, 'e) expr list)

val create_exp_positive_reqs : 'a context -> 'a term list list -> 'a formula
val preify : 'a context -> (symbol * symbol) list -> ('a, 'b) expr -> ('a, 'b) expr
val postify : 'a context -> (symbol * symbol) list -> ('a, 'b) expr -> ('a, 'b) expr 

val unify : M.t list -> M.t
val ident_matrix_syms : 'a context -> (symbol * symbol) list -> M.t
val exp_other_reset_helper : 'a context -> 'a term -> 'a term list -> 'a term list list -> int -> 'a formula
val term_list : 'a context -> M.t list -> (symbol * Symbol.Map.key) list -> (('a, typ_arith) expr * 'a term) list
val gamma_transformer : 'a context -> ('a term * 'a term) list -> transformer -> 'a formula
val alpha_hat  : 'a context -> 'a formula -> ('b * symbol) list -> (Symbol.Map.key * symbol) list -> 'a formula list -> 'c t
val coproduct : 'b -> 'c t -> 'd t -> 'a t
val mk_bottom : 'a context -> ('b * symbol) list -> 'c t
val coprod_compute_image : TSet.t -> M.t list -> TSet.t
val coprod_find_transformation : M.t list -> M.t list -> Linear.QQMatrix.t list * Linear.QQMatrix.t list * M.t list
val find_invariants : 'a context -> (symbol * symbol) list -> 'a formula -> 'a formula * 'a formula list * bool
