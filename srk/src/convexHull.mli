open Syntax

type t = DD.closed DD.t

val dump_hull: bool ref
val dump_hull_prefix : string ref

(** False by default unless otherwise set. *)
val abstraction_algorithm: PolyhedronLatticeTiling.abstraction_algorithm ref

val abstract : 'a Abstract.Solver.t ->
               ?man:(DD.closed Apron.Manager.t) ->
               ?bottom:(t option) ->
               'a arith_term array ->
               t

val of_model_lira: 'a Abstract.Solver.t ->
                   (DD.closed Apron.Manager.t) ->
                   ('a arith_term) array ->
                   'a Abstract.smt_model ->
                   DD.closed DD.t

val of_model_lirr : 'a Abstract.Solver.t ->
  (DD.closed Apron.Manager.t) ->
  ('a arith_term) array ->
  'a Abstract.smt_model ->
  DD.closed DD.t
