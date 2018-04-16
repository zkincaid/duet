open Syntax
open BatPervasives

include Log.Make(struct let name = "srk.simplify" end)

module TermPolynomial = struct
  type 'a polynomial_context =
    { srk : 'a context;
      int_of : 'a term -> int;
      of_int : int -> 'a term }

  module Mvp = Polynomial.Mvp
  module Monomial = Polynomial.Monomial
  module DynArray = BatDynArray

  type 'a t = Mvp.t

  let mk_context srk =
    let table = Expr.HT.create 991 in
    let enum = DynArray.create () in
    let of_int = DynArray.get enum in
    let int_of term =
      if Expr.HT.mem table term then
        Expr.HT.find table term
      else
        let id = DynArray.length enum in
        DynArray.add enum term;
        Expr.HT.add table term id;
        id
    in
    { srk; of_int; int_of }

  let rec of_term ctx =
    let srk = ctx.srk in
    let mvp_term = Mvp.of_dim % ctx.int_of in
    let alg = function
      | `Add xs -> List.fold_left Mvp.add Mvp.zero xs
      | `Mul xs -> List.fold_left Mvp.mul Mvp.one xs
      | `Real k -> Mvp.scalar k
      | `Unop (`Neg, x) -> Mvp.negate x
      | `Unop (`Floor, x) -> mvp_term (mk_floor srk (term_of ctx x))
      | `App (f, args) -> mvp_term (mk_app srk f args)
      | `Binop (`Div, x, y) ->
        mvp_term (mk_div srk (term_of ctx x) (term_of ctx y))
      | `Binop (`Mod, x, y) ->
        mvp_term (mk_mod srk (term_of ctx x) (term_of ctx y))
      | `Ite (cond, bthen, belse) ->
        mvp_term (mk_ite srk cond (term_of ctx bthen) (term_of ctx belse))
      | `Var (v, typ) -> mvp_term (mk_var srk v (typ :> typ_fo))
    in
    Term.eval srk alg
    
  and term_of ctx p =
    let srk = ctx.srk in
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
            []
            (Monomial.enum monomial)
        in
        mk_mul srk ((mk_real srk coeff)::product))
    |> BatList.of_enum
    |> mk_add ctx.srk
end

let simplify_terms_rewriter srk =
  let ctx = TermPolynomial.mk_context srk in
  fun expr ->
    match destruct srk expr with
    | `Atom (op, s, t) ->
      let simplified_term =
        let polynomial =
          TermPolynomial.of_term ctx (mk_sub srk s t)
        in
        let c = TermPolynomial.Mvp.content polynomial in
        let polynomial =
          if QQ.equal c QQ.zero then
            polynomial
          else
            TermPolynomial.Mvp.scalar_mul (QQ.inverse (QQ.abs c)) polynomial
        in
        TermPolynomial.term_of ctx polynomial
      in
      let zero = mk_real srk QQ.zero in
      let result = match op with
        | `Leq -> mk_leq srk simplified_term zero
        | `Lt -> mk_lt srk simplified_term zero
        | `Eq -> mk_eq srk simplified_term zero 
      in
      (result :> ('a,typ_fo) expr)
    | _ -> expr

let simplify_terms srk expr =
  rewrite srk ~up:(simplify_terms_rewriter srk) expr

let purify_rewriter srk table =
  fun expr ->
    match destruct srk expr with
    | `Quantify (_, _, _, _) -> invalid_arg "purify: free variable"
    | `App (func, []) -> expr
    | `App (func, args) ->
      let sym =
        try
          Expr.HT.find table expr
        with Not_found ->
          let sym = mk_symbol srk ~name:"uninterp" (expr_typ srk expr) in
          Expr.HT.add table expr sym;
          sym
      in
      mk_const srk sym
    | _ -> expr

let purify srk expr =
  let table = Expr.HT.create 991 in
  let expr' = rewrite srk ~up:(purify_rewriter srk table) expr in
  let map =
    BatEnum.fold
      (fun map (term, sym) -> Symbol.Map.add sym term map)
      Symbol.Map.empty
      (Expr.HT.enum table)
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
