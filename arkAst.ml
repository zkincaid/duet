module Ctx = Syntax.Make(Syntax.TypedString)()

type term = Ctx.term
type formula = Ctx.formula

let mk_quantified mkq ks phi =
  let ks_rev = List.rev ks in
  let subst k =
    match BatList.index_of k ks_rev with
    | Some i -> Ctx.mk_var i `TyReal
    | None -> Ctx.mk_const k
  in
  let show_const = Apak.Putil.mk_show Ctx.pp_const in
  let phi = Ctx.Formula.substitute_const subst phi in
  List.fold_right (fun k phi -> mkq (show_const k) `TyReal phi) ks phi

let mk_exists ks phi = mk_quantified (fun name -> Ctx.mk_exists ~name) ks phi
let mk_forall ks phi = mk_quantified (fun name -> Ctx.mk_forall ~name) ks phi
