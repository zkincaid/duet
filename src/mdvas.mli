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

type 'a t = { v : vas; alphas : M.t list; invars : 'a formula list; invarmaxk : bool}

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
val map_terms : 'a context -> symbol list -> 'a term list
val exp_base_helper : 'a context -> (symbol * Symbol.Map.key) list -> 'a term ->
  M.t list -> transformer list -> 'a formula list -> bool -> 
  'a formula * (('a term list * (('a, 'b) expr * Z.dim) list * ('a, 'c) expr * ('a, 'd) expr)
                  list * 'a term list list * ('a, 'e) expr list)
                                                             
val create_exp_positive_reqs : 'a context -> 'a term list list -> 'a formula
val preify : 'a context -> (symbol * symbol) list -> ('a, 'b) expr -> ('a, 'b) expr
val postify : 'a context -> (symbol * symbol) list -> ('a, 'b) expr -> ('a, 'b) expr 

val unify : M.t list -> M.t
val ident_matrix : 'a context -> (symbol * symbol) list -> M.t

val exp_other_reset : 'a context -> 'a term -> 'a term list -> 'a term list list -> int -> 'a formula

module Mdvass : sig
  module Int = SrkUtil.Int
  module VassGraph : sig
    type t = vas array array

    module V = Int
  end
    type 'a t
  val compute_edges : 'a context -> vas -> (symbol * symbol) list -> M.t list -> ('a formula) array -> ('a formula) -> vas array array
  val exp_post_conds_on_transformers : 'a context -> 'a formula array ->
           (int * transformer * int) list ->
           (TSet.t * 'b) array -> 'a term list ->
           M.t list -> (symbol * symbol) list -> 'a term -> 'a formula
end
