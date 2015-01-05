open ArkPervasives

type interval deriving (Show,Compare)

val make : QQ.t option -> QQ.t option -> interval
val make_bounded : QQ.t -> QQ.t -> interval
val top : interval
val bottom : interval
val const : QQ.t -> interval
val zero : interval
val const_of : interval -> QQ.t option

val negate : interval -> interval

val format : Format.formatter -> interval -> unit
val show : interval -> string

val compare : interval -> interval -> int
val equal : interval -> interval -> bool

val mul : interval -> interval -> interval
val div : interval -> interval -> interval
val modulo : interval -> interval -> interval
val add : interval -> interval -> interval
val floor : interval -> interval

val join : interval -> interval -> interval
val meet : interval -> interval -> interval
val leq : interval -> interval -> bool

val is_nonnegative : interval -> bool
val is_nonpositive : interval -> bool
val is_negative : interval -> bool
val is_positive : interval -> bool
val elem : QQ.t -> interval -> bool

val lower : interval -> QQ.t option
val upper : interval -> QQ.t option

val of_apron : Apron.Interval.t -> interval
val apron_of : interval -> Apron.Interval.t
