open Syntax
open Transition

module MakeSolver (Ctx : Syntax.Context) (Var : Transition.Var) : sig
  type t
  type triple

  val mk_solver : t
  val register_triple : t -> triple -> unit
  val check_solution : t -> [ `Sat | `Unsat | `Unknown ]
  val get_solution : t -> triple list
end
