open Syntax
module V = Linear.QQVector
module M = Linear.QQMatrix
module Z = Linear.ZZVector

type 'a t = 'a formula

type qfp =  [ `Exists of string * Syntax.typ_fo
            | `Forall of string * Syntax.typ_fo] list


val to_mfa : 'a context -> 'a formula -> qfp * 'a t

val add_prefix : 'a context -> qfp * 'a t -> 'a t
val mfa_to_lia : 'a context -> (qfp * 'a formula) -> Symbol.Set.t -> 'a t
