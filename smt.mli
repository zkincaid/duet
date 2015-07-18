exception Unknown_result

module type TranslationContext = sig
  include Syntax.BuilderContext
  include Syntax.EvalContext with type term := term and type formula := formula
end

module MakeZ3  (Opt : sig val opts : (string * string) list end)() :
  TranslationContext

module MakeSolver
    (C : TranslationContext)
    (Opt : sig val opts : (string * string) list end)
    () : sig

  type solver
  type model

  (** May raise [Unknown_result]. *)
  val implies : C.formula -> C.formula -> bool

  val is_sat : C.formula -> [ `Sat | `Unsat | `Unknown ]
  val get_model : C.formula -> [ `Sat of model | `Unsat | `Unknown ]
  val interpolate_seq : C.formula list ->
    [ `Sat of model | `Unsat of C.formula list | `Unknown ]

  module Solver : sig
    val mk_solver : unit -> solver
    val add : solver -> C.formula list -> unit
    val push : solver -> unit
    val pop : solver -> int -> unit
    val check : solver -> C.formula list -> [ `Sat | `Unsat | `Unknown ]
    val get_model : solver -> [ `Sat of model | `Unsat | `Unknown ]
  end

  module Model : sig
    val eval_int : model -> C.term -> ZZ.t
    val eval_real : model -> C.term -> QQ.t
    val sat : model -> C.formula -> bool
    val to_string : model -> string
  end
end
