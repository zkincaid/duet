open Syntax
open BatPervasives

include Log.Make(struct let name = "ark.simplify" end)

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

module ExprVec = Linear.ExprQQVector
let qe_partial_implicant ark p implicant =
  let subst map expr =
    substitute_const ark (fun sym ->
        try Symbol.Map.find sym map
        with Not_found -> mk_const ark sym)
      expr
  in
  let (rewrite, implicant) =
    List.fold_left (fun (rewrite, implicant) atom ->
        match Interpretation.destruct_atom ark atom with
        | `Comparison (`Eq, x, y) ->
          let diff =
            ExprVec.of_term ark (subst rewrite (mk_sub ark x y))
          in
          (* A symbol can be eliminated if it appears in the equation, and
             isn't *trapped*.  A symbol is trapped if it appears as subterm of
             another term.  *)
          let (trapped, elim) =
            BatEnum.fold (fun (trapped, elim) (term, _) ->
                match Term.destruct ark term with
                | `App (sym, []) ->
                  if p sym then (trapped, elim)
                  else (trapped, Symbol.Set.add sym elim)
                | _ -> (Symbol.Set.union trapped (symbols term)), elim)
              (Symbol.Set.empty, Symbol.Set.empty)
              (ExprVec.enum diff)
          in
          let elim = Symbol.Set.diff elim trapped in
          if Symbol.Set.is_empty elim then
            (rewrite, atom::implicant)
          else
            let sym = Symbol.Set.min_elt elim in
            let (coeff, rest) = ExprVec.pivot (mk_const ark sym) diff in
            let rhs =
              ExprVec.scalar_mul (QQ.negate (QQ.inverse coeff)) rest
              |> ExprVec.term_of ark
            in
            let rewrite =
              Symbol.Map.map
                      (substitute_const ark (fun sym' ->
                    if sym = sym' then rhs
                    else mk_const ark sym'))
                      rewrite
            in
            (Symbol.Map.add sym rhs rewrite, implicant)
        | _ -> (rewrite, atom::implicant))
      (Symbol.Map.empty, [])
      implicant
  in
  List.map (subst rewrite) implicant

let purify_rewriter ark table =
  fun expr ->
    match destruct ark expr with
    | `Quantify (_, _, _, _) -> invalid_arg "purify: free variable"
    | `App (func, []) -> expr
    | `App (func, args) ->
      let sym =
        try
          ExprHT.find table expr
        with Not_found ->
          let sym = mk_symbol ark ~name:"uninterp" (expr_typ ark expr) in
          ExprHT.add table expr sym;
          sym
      in
      mk_const ark sym
    | _ -> expr

let purify ark expr =
  let table = ExprHT.create 991 in
  let expr' = rewrite ark ~up:(purify_rewriter ark table) expr in
  let map =
    BatEnum.fold
      (fun map (term, sym) -> Symbol.Map.add sym term map)
      Symbol.Map.empty
      (ExprHT.enum table)
  in
  (expr', map)

module SymDS = DisjointSet.Make(struct
    include Symbol
    let hash = Hashtbl.hash
    let equal = (=)
  end)
let partition_implicant implicant =
  let (zero_group, implicant) =
    List.partition (fun atom -> Symbol.Set.is_empty (symbols atom)) implicant
  in
  if implicant = [] then
    [zero_group]
  else begin
    let ds = SymDS.create 991 in
    implicant |> List.iter (fun atom ->
        let (sym, rest) = Symbol.Set.pop (symbols atom) in
        let rep = SymDS.find ds sym in
        Symbol.Set.iter (fun sym' -> ignore (SymDS.union (SymDS.find ds sym') rep)) rest);
    let rev_map =
      SymDS.reverse_map ds Symbol.Set.empty Symbol.Set.add
    in
    let find_rep symbol = Symbol.Set.choose (rev_map symbol) in
    let map =
      List.fold_left (fun map atom ->
          let equiv_class = find_rep (Symbol.Set.choose (symbols atom)) in
          if Symbol.Map.mem equiv_class map then
            Symbol.Map.add equiv_class (atom::(Symbol.Map.find equiv_class map)) map
          else
            Symbol.Map.add equiv_class [atom] map)
        Symbol.Map.empty
        implicant
    in
    let partitioned_implicant =
      BatList.of_enum (Symbol.Map.values map)
    in
    if zero_group = [] then
      partitioned_implicant
    else
      zero_group::partitioned_implicant
  end
