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
val remove_row: 'a t -> int -> int -> 'a t
val postify : 'a context -> (symbol * symbol) list -> 'a formula -> 'a formula
val map_terms : 'a context -> symbol list -> 'a term list
val exp_base_helper : 'a context -> (symbol * symbol) list -> 'a term -> 
  M.t list -> transformer list -> 'a formula list -> bool -> 'a formula * ((('a, 'b) expr list * (('a, 'c) expr * int) list *
                                                               ('a, 'd) expr * ('a, 'e) expr) list * 
                                                              'a term list list * ('a, 'f) expr list *
                                                              ('a, 'g) expr list) 
val create_exp_positive_reqs : 'a context -> 'a term list list -> 'a formula


module Mdvass : sig
  module Int = SrkUtil.Int
  module VassGraph : sig
    type t = vas array array

    module V = Int
  end
    type 'a t
  val pp : 'a context -> (symbol * symbol) list -> Format.formatter -> 'a t -> unit
  val exp : 'a context -> (symbol * symbol) list -> 'a term -> 'a t -> 'a formula
  val join : 'a context -> (symbol * symbol) list -> 'a t -> 'a t -> 'a t
  val widen : 'a context -> (symbol * symbol) list -> 'a t -> 'a t -> 'a t
  val equal : 'a context -> (symbol * symbol) list -> 'a t -> 'a t -> bool
  val abstract : ?exists:(symbol -> bool) ->
    'a context ->
    (symbol * symbol) list ->
    'a formula ->
    'a t
  val get_intersect_cube_labeling : 'a context -> 'a formula -> (symbol -> bool) -> (symbol * symbol) list -> ('a formula) array
  val compute_edges : 'a context -> vas -> (symbol * symbol) list -> M.t list -> ('a formula) array -> ('a formula) -> vas array array
  val create_n_vars : 'a context -> int -> symbol list -> string -> symbol list
  val exp_nvars_eq_loop_counter : 'a context -> 'a term list -> 'a term -> 'a formula
  val exp_kvarst_less_nvarst : 'a context -> 'a term list -> 'a term list list -> 'a formula
  val get_reachable_trans : VassGraph.t -> (TSet.t * VassGraph.V.t list) array
  val exp_post_conds_on_transformers : 'a context -> 'a formula array ->
           (int * transformer * int) list ->
           (TSet.t * 'b) array -> 'a term list ->
           M.t list -> (symbol * symbol) list -> 'a term -> 'a formula
  val create_es_et : 'a context -> int -> (('a, 'b) expr * ('a, 'c) expr) list
  val exp_consv_of_flow : 'a context -> 'a term list array -> 'a term list array -> ('a term * 'a term) list -> 'a formula
  val exp_one_in_out_flow : 'a context -> ('a term * 'a term) list -> 'a term list -> 'a formula
  val exp_each_ests_one_or_zero : 'a context -> ('a term * 'a term) list -> 'a formula
  val exp_pre_post_conds : 'a context -> ('a term * 'a term) list -> 'a formula array -> (symbol * symbol) list -> 'a formula
end
