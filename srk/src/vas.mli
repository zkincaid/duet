(** Rational Vector Addition System with Resets Abstract Domain.  A
   rational vector addition system with resets is a set of \{0,
   1\}{^n} x QQ{^n} vector pairs. Each object describes a reset or
   increment to n counters. *)
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
val mk_bottom : (symbol * symbol) list -> symbol list -> 'a t
val matrixify_vectorize_term_list : 'a context -> 'a Syntax.term list -> M.t * V.t

(* TODO: remove exp_base_helper *)
val exp_base_helper : 'a context -> (symbol * Symbol.Map.key) list -> 'a term ->
  M.t list -> transformer list -> 
  'a formula * (('a term list * ('a term * Z.dim) list * 'a term * 'a term)
                  list * 'a term list list * 'a term list)

(* TODO: remove exp_other_reset_helper *)
val exp_other_reset_helper : 'a context -> 'a term -> 'a term list -> 'a term list list 
  -> int -> 'a formula

val term_list : 'a context -> M.t list -> (symbol * Symbol.Map.key) list -> 
  (('a, typ_arith) expr * 'a term) list
val gamma_transformer : 'a context -> ('a term * 'a term) list -> transformer -> 'a formula
val alpha_hat  : 'a context -> 'a formula -> (symbol * symbol) list -> symbol list -> 'c t
val coprod_compute_image : TSet.t -> M.t list -> TSet.t
val coprod_find_transformation : M.t list -> M.t list -> 
  Linear.QQMatrix.t list * Linear.QQMatrix.t list * M.t list

