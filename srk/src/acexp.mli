open Syntax
open Linear

type kind = Commute | Reset | Ignore

type phased_segment = {
  sim1 : QQMatrix.t;
  sim2 : QQMatrix.t;
  phase1 : QQMatrix.t array;
  phase2 : (kind * QQMatrix.t) array
}

type 'a t = phased_segment list

val pp : 'a context -> (symbol * symbol) list -> Format.formatter -> 'a t -> unit
   
val exp : 'a context -> (symbol * symbol) list -> 'a term -> 'a t -> 'a formula
