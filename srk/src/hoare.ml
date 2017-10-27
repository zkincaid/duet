open Syntax
open Transition
open SrkZ3
open BatPervasives

include Log.Make(struct let name = "srk.hoare" end)

module MakeSolver(Ctx : Syntax.Context) (Var : Transition.Var) = struct

  module Infix = Syntax.Infix(Ctx)
  module Transition = Transition.Make(Ctx)(Var)

  type transition = Transition.t
  type formula = Ctx.formula
  type triple = (formula list) * transition * (formula list)

  module DA = BatDynArray

  let srk = Ctx.context

  let pp_triple formatter (pre, trans, post) =
    let open Format in
    fprintf formatter "{";
    SrkUtil.pp_print_enum ~pp_sep:(fun formatter () -> fprintf formatter " /\\ ")
                          (Expr.pp srk)
                          formatter
                          (BatList.enum pre);
    fprintf formatter "} ";
    Transition.pp formatter trans;
    fprintf formatter " {";
    SrkUtil.pp_print_enum ~pp_sep:(fun formatter () -> fprintf formatter " /\\ ")
                          (Expr.pp srk)
                          formatter
                          (BatList.enum post);
    fprintf formatter "}"

  type t = {
      smt_ctx : Ctx.t z3_context;
      solver : Ctx.t CHC.solver;
      triples : triple DA.t;
    }

  let mk_solver () =
    let smt_ctx = mk_context srk [] in
    { smt_ctx = smt_ctx;
      solver = CHC.mk_solver smt_ctx;
      triples = DA.create();
    }

  let get_solver solver =
    solver.solver

  (*
     register {[P(...) ; Q(...); x = 3; y < x]} transition {[R(...); S(...)]}
     as P(...) /\ Q(...) /\ x = 3 /\ y < x /\ transition.guard --> R(...)
        P(...) /\ Q(...) /\ x = 3 /\ y < x /\ transition.guard --> S(...)
   *)
  let register_triple solver (pre, trans, post) =
    let rec register_formulas formulas =
      match formulas with
      | [] -> ()
      | form :: forms ->
         begin
           match destruct srk form with
           | `App (p, _) -> CHC.register_relation solver.solver p
           | _ -> ()
         end; register_formulas forms
    in
    let fresh =
      let ind : int ref = ref (-1) in
      Memo.memo (fun sym ->
          match typ_symbol srk sym with
          | `TyInt  -> incr ind; mk_var srk (!ind) `TyInt
          | `TyReal -> incr ind; mk_var srk (!ind) `TyReal
          | `TyBool -> incr ind; mk_var srk (!ind) `TyBool
          | _ -> mk_const srk sym
        )
    in
    let body = (* conjunct all preconditions and guard of the transition *)
      let rec go rels =
        match rels with
        | [] -> substitute_const srk fresh (Transition.guard trans)
        | rel :: rels -> mk_and srk [(substitute_const srk fresh rel); go rels]
      in go pre
    in
    let add_rules posts =
      let postify sym = 
        match Var.of_symbol sym with
        | Some v when Transition.mem_transform v trans ->
             substitute_const srk fresh (Transition.get_transform v trans)
        | _ -> fresh sym
      in
      let rec go posts = (* add a rule for each post condition *)
        match posts with
        | [] -> ()
        | post :: posts -> CHC.add_rule solver.solver body (substitute_const srk postify post); go posts
      in
      go posts
    in
    DA.add solver.triples (pre, trans, post);
    register_formulas pre;
    register_formulas post;
    add_rules post

  let check_solution solver = CHC.check solver.solver []

  let get_solution solver =
    let get_triple trips (pre, trans, post) =
      let rec subst =
        let rewriter expr =
          match destruct srk expr with
          | `App (_, []) -> expr
          | `App (rel, args) ->
             (substitute srk
                (fun (v, _) -> List.nth args v)
                (CHC.get_solution solver.solver rel) :> ('a, typ_fo) Syntax.expr)
          | _ -> expr
        in
        function
        | [] -> []
        | rel :: rels ->
           (rewrite srk ~down:rewriter rel) :: (subst rels)
      in
      (subst pre, trans, subst post) :: trips
    in
    List.rev (DA.fold_left get_triple [] solver.triples)

end
