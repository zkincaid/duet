open Syntax
open Transition

module type Letter = sig
  type t
  type trans
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit

  val transition_of : t -> trans
end

module MakeSolver (Ctx : Syntax.Context) (Var : Transition.Var) (Ltr : Letter with type trans = Transition.Make(Ctx)(Var).t) : sig
  type t
  type triple

  val pp_triple : Format.formatter -> triple -> unit

  val mk_solver : unit -> t
  val get_solver : t -> Ctx.t SrkZ3.CHC.solver
  val register_triple : t -> triple -> unit
  val check_solution : t -> [ `Sat | `Unsat | `Unknown ]
  val verify_solution : t -> [ `Valid | `Invalid | `Unknown ]
  val get_solution : t -> triple list
  val get_symbolic : t -> triple list
  val simplify : triple -> triple list
  val reduce_vars : t -> unit
                                  
end with type triple = (Ctx.formula list) * Ltr.t * (Ctx.formula list)
