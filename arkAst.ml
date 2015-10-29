module Ctx = Syntax.MakeContext ()

type term = Ctx.term
type formula = Ctx.formula

let mk_quantified mkq ks phi =
  let ks_rev = List.rev ks in
  let subst k =
    match BatList.index_of k ks_rev with
    | Some i -> Ctx.mk_var i `TyReal
    | None -> Ctx.mk_const k
  in
  let phi = Syntax.substitute_const Ctx.context subst phi in
  List.fold_right
    (fun k phi -> mkq (Syntax.show_symbol Ctx.context k) `TyReal phi)
    ks
    phi

let mk_exists ks phi = mk_quantified (fun name -> Ctx.mk_exists ~name) ks phi
let mk_forall ks phi = mk_quantified (fun name -> Ctx.mk_forall ~name) ks phi
