open Syntax
open BatPervasives
open Apak

include Log.Make(struct let name = "ark.simplify" end)

(*
let simplify_terms_rewriter ark expr =
  match destruct ark expr with
  | `Atom (op, s, t) ->
    let simplified_term =
      ExprVec.term_of ark (ExprVec.of_term ark (mk_sub ark s t))
    in
    let zero = mk_real ark QQ.zero in
    let result = match op with
      | `Leq -> mk_leq ark simplified_term zero
      | `Lt -> mk_lt ark simplified_term zero
      | `Eq -> mk_eq ark simplified_term zero 
    in
    (result :> ('a,typ_fo) expr)
  | _ -> expr

let simplify_terms ark expr =
  rewrite ark ~up:(simplify_terms_rewriter ark) expr
*)

module TermPolynomial = struct
  type 'a polynomial_context =
    { ark : 'a context;
      int_of : 'a term -> int;
      of_int : int -> 'a term }

  module Mvp = Polynomial.Mvp
  module Monomial = Polynomial.Monomial
  module DynArray = BatDynArray

  type 'a t = Mvp.t

  let mk_context ark =
    let table = ExprHT.create 991 in
    let enum = DynArray.create () in
    let of_int = DynArray.get enum in
    let int_of term =
      if ExprHT.mem table term then
        ExprHT.find table term
      else
        let id = DynArray.length enum in
        DynArray.add enum term;
        ExprHT.add table term id;
        id
    in
    { ark; of_int; int_of }

  let rec of_term ctx =
    let ark = ctx.ark in
    let mvp_term = Mvp.of_dim % ctx.int_of in
    let alg = function
      | `Add xs -> List.fold_left Mvp.add Mvp.zero xs
      | `Mul xs -> List.fold_left Mvp.mul Mvp.one xs
      | `Real k -> Mvp.scalar k
      | `Unop (`Neg, x) -> Mvp.negate x
      | `Unop (`Floor, x) -> mvp_term (mk_floor ark (term_of ctx x))
      | `App (f, args) -> mvp_term (mk_app ark f args)
      | `Binop (`Div, x, y) ->
        mvp_term (mk_div ark (term_of ctx x) (term_of ctx y))
      | `Binop (`Mod, x, y) ->
        mvp_term (mk_mod ark (term_of ctx x) (term_of ctx y))
      | `Ite (cond, bthen, belse) ->
        mvp_term (mk_ite ark cond (term_of ctx bthen) (term_of ctx belse))
      | `Var (v, typ) -> mvp_term (mk_var ark v (typ :> typ_fo))
    in
    Term.eval ark alg
    
  and term_of ctx p =
    let ark = ctx.ark in
    (Mvp.enum p)
    /@ (fun (coeff, monomial) ->
        let product =
          BatEnum.fold
            (fun product (dim, power) ->
               let term = ctx.of_int dim in
               BatEnum.fold
                 (fun product _ -> term::product)
                 product
                 (1 -- power))
            [mk_real ark coeff]
            (Monomial.enum monomial)
        in
        mk_mul ark product)
    |> BatList.of_enum
    |> mk_add ctx.ark
end

let simplify_terms_rewriter ark =
  let ctx = TermPolynomial.mk_context ark in
  fun expr ->
    match destruct ark expr with
    | `Atom (op, s, t) ->
      let simplified_term =
        TermPolynomial.term_of ctx
          (TermPolynomial.of_term ctx (mk_sub ark s t))
      in
      let zero = mk_real ark QQ.zero in
      let result = match op with
        | `Leq -> mk_leq ark simplified_term zero
        | `Lt -> mk_lt ark simplified_term zero
        | `Eq -> mk_eq ark simplified_term zero 
      in
      (result :> ('a,typ_fo) expr)
    | _ -> expr

let simplify_terms ark expr =
  rewrite ark ~up:(simplify_terms_rewriter ark) expr
