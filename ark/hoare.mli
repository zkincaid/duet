open Syntax
open Transition

module MakeSolver (Ctx : Syntax.Context) (Var : Transition.Var) : sig
  type t
  type triple

  val pp_triple : Format.formatter -> triple -> unit

  val mk_solver : t
  val get_solver : t -> Ctx.t ArkZ3.CHC.solver
  val register_triple : t -> triple -> unit
  val check_solution : t -> [ `Sat | `Unsat | `Unknown ]
  val get_solution : t -> triple list
end with type triple = (Ctx.formula list) * Transition.Make(Ctx)(Var).t * (Ctx.formula list)
