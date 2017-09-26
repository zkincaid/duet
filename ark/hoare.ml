open Syntax
open Transition
open ArkZ3
open BatPervasives

include Log.Make(struct let name = "ark.hoare" end)

module MakeSolver(Ctx : Syntax.Context) (Var : Transition.Var) = struct

  module Infix = Syntax.Infix(Ctx)
  module Transition = Transition.Make(Ctx)(Var)

  type transition = Transition.t
  type formula = Ctx.formula
  type triple = (formula list) * transition * (formula list)

  module DA = BatDynArray

  let ark = Ctx.context

  let pp_triple formatter (pre, trans, post) =
    let open Format in
    fprintf formatter "{";
    ArkUtil.pp_print_enum ~pp_sep:(fun formatter () -> fprintf formatter " /\\ ")
                          (Expr.pp ark)
                          formatter
                          (BatList.enum pre);
    fprintf formatter "} ";
    Transition.pp formatter trans;
    fprintf formatter " {";
    ArkUtil.pp_print_enum ~pp_sep:(fun formatter () -> fprintf formatter " /\\ ")
                          (Expr.pp ark)
                          formatter
                          (BatList.enum post);
    fprintf formatter "}"

  type t = {
      smt_ctx : Ctx.t z3_context;
      solver : Ctx.t CHC.solver;
      triples : triple DA.t;
    }

  let mk_solver =
    let smt_ctx = mk_context ark [] in
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
           match destruct ark form with
           | `App (p, _) -> CHC.register_relation solver.solver p
           | _ -> ()
         end; register_formulas forms
    in
    let fresh =
      let ind : int ref = ref (-1) in
      Memo.memo (fun sym ->
          match typ_symbol ark sym with
          | `TyInt  -> incr ind; mk_var ark (!ind) `TyInt
          | `TyReal -> incr ind; mk_var ark (!ind) `TyReal
          | `TyBool -> incr ind; mk_var ark (!ind) `TyBool
          | _ -> mk_const ark sym
        )
    in
    let body = (* conjunct all preconditions and guard of the transition *)
      let rec go rels =
        match rels with
        | [] -> substitute_const ark fresh (Transition.guard trans)
        | rel :: rels -> mk_and ark [(substitute_const ark fresh rel); go rels]
      in go pre
    in
    let add_rules posts =
      let postify sym = 
        match Var.of_symbol sym with
        | Some v when Transition.mem_transform v trans ->
           substitute_const ark fresh (Transition.get_transform v trans)
        | _ -> fresh sym
      in
      let rec go posts = (* add a rule for each post condition *)
        match posts with
        | [] -> ()
        | post :: posts -> CHC.add_rule solver.solver body (substitute_const ark postify post);
                           go posts
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
          match destruct ark expr with
          | `App (_, []) -> expr
          | `App (rel, args) ->
             (substitute ark
                (fun (v, _) -> List.nth args v)
                (CHC.get_solution solver.solver rel) :> ('a, typ_fo) Syntax.expr)
          | _ -> expr
        in
        function
        | [] -> []
        | rel :: rels ->
           (rewrite ark ~down:rewriter rel) :: (subst rels)
      in
      (subst pre, trans, subst post) :: trips
    in
    DA.fold_left get_triple [] solver.triples

end
