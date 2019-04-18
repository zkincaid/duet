(** Rational Vector Addition System with Resets Abstract Domain.
 * A rational vector addition system with resets is a set of 
 * {0, 1}^n x Q^n vector pairs. Each object describes
 * a reset or increment to n counters. *)
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
type 'a t = { v : vas; s_lst : M.t list}
val gamma : 'a context ->  'a t -> (symbol * symbol) list -> 'a formula
val abstract : ?exists:(symbol -> bool) -> 'a context -> (symbol * symbol) list -> 
  'a formula -> 'a t
val pp : 'a context -> (symbol * symbol) list -> Format.formatter -> 'a t -> unit
val exp : 'a context -> (symbol * symbol) list -> 'a term -> 'a t -> 'a formula
val join : 'a context -> (symbol * symbol) list -> 'a t -> 'a t -> 'a t
val widen : 'a context -> (symbol * symbol) list -> 'a t -> 'a t -> 'a t
val equal : 'a context -> (symbol * symbol) list -> 'a t -> 'a t -> bool
val exp_base_helper : 'a context -> (symbol * Symbol.Map.key) list -> 'a term ->
  M.t list -> transformer list -> 
  'a formula * (('a term list * (('a, 'b) expr * Z.dim) list * ('a, 'c) expr * ('a, 'd) expr)
                  list * 'a term list list * ('a, 'e) expr list)
val create_exp_positive_reqs : 'a context -> 'a term list list -> 'a formula
val preify : 'a context -> (symbol * symbol) list -> ('a, 'b) expr -> ('a, 'b) expr
val postify : 'a context -> (symbol * symbol) list -> ('a, 'b) expr -> ('a, 'b) expr 
val unify : M.t list -> M.t
val ident_matrix_syms : 'a context -> (symbol * symbol) list -> M.t
val exp_other_reset_helper : 'a context -> 'a term -> 'a term list -> 'a term list list 
  -> int -> 'a formula
val term_list : 'a context -> M.t list -> (symbol * Symbol.Map.key) list -> 
  (('a, typ_arith) expr * 'a term) list
val gamma_transformer : 'a context -> ('a term * 'a term) list -> transformer -> 'a formula
val alpha_hat  : 'a context -> 'a formula -> ('b * symbol) list -> 
  (Symbol.Map.key * symbol) list -> 'a formula list -> 'c t
val coprod_compute_image : TSet.t -> M.t list -> TSet.t
val coprod_find_transformation : M.t list -> M.t list -> 
  Linear.QQMatrix.t list * Linear.QQMatrix.t list * M.t list
