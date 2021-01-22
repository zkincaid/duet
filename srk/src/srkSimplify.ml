open Syntax
open BatPervasives

include Log.Make(struct let name = "srk.simplify" end)

module RationalTerm = struct
  type 'a rt_context =
    { srk : 'a context;
      int_of : 'a term -> int;
      of_int : int -> 'a term }

  module QQXs = Polynomial.QQXs
  module Monomial = Polynomial.Monomial
  module DynArray = BatDynArray

  (* A rational term is polynomial divided by a monomial.  TODO:
     Denominator ought to be a polynomial too. *)
  type 'a t =
    { num : QQXs.t;     (* Numerator *)
      den : Monomial.t  (* Denominator *) }

  let scalar k = { num = QQXs.scalar k; den = Monomial.one }

  let zero = scalar QQ.zero

  let one = scalar QQ.one

  let add f g =
    let den = Monomial.lcm f.den g.den in
    let f_mul, g_mul =
      match Monomial.div den f.den, Monomial.div den g.den with
      | Some f_den, Some g_den ->
        (QQXs.add_term QQ.one f_den QQXs.zero,
         QQXs.add_term QQ.one g_den QQXs.zero)
      | _, _ -> assert false
    in
    let num =
      QQXs.add (QQXs.mul f_mul f.num) (QQXs.mul g_mul g.num)
    in
    { num; den }

  let negate f = { f with num = QQXs.negate f.num }

  let mul f g =
    { num = QQXs.mul f.num g.num;
      den = Monomial.mul f.den g.den }

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
    let rat_term (term : 'a term) : 'a t =
      { num = QQXs.of_dim (ctx.int_of term);
        den = Monomial.one }
    in
    let alg = function
      | `Add xs -> List.fold_left add zero xs
      | `Mul xs -> List.fold_left mul one xs
      | `Real k -> scalar k
      | `Unop (`Neg, x) -> negate x
      | `Unop (`Floor, x) -> rat_term (mk_floor srk (term_of ctx x))
      | `App (f, args) -> rat_term (mk_app srk f args)
      | `Binop (`Div, x, y) ->
        { num = x.num;
          den = Monomial.mul_term (ctx.int_of (term_of ctx y)) 1 x.den }
      | `Binop (`Mod, x, y) ->
        rat_term (mk_mod srk (term_of ctx x) (term_of ctx y))
      | `Ite (cond, bthen, belse) ->
        rat_term (mk_ite srk cond (term_of ctx bthen) (term_of ctx belse))
      | `Var (v, typ) -> rat_term (mk_var srk v (typ :> typ_fo))
    in
    Term.eval srk alg
    
  and term_of ctx p =
    let srk = ctx.srk in
    let num =
      QQXs.term_of srk ctx.of_int p.num
    in
    mk_div srk num (Monomial.term_of srk ctx.of_int p.den)

  let num x = x.num
  let den x = x.den
end

let simplify_term srk term =
  let ctx = RationalTerm.mk_context srk in
  let rt =
    RationalTerm.of_term ctx term
  in
  let c = RationalTerm.QQXs.content (RationalTerm.num rt) in
  let result =
    if QQ.equal c QQ.zero then
      rt
    else
      let open RationalTerm in
      { rt with
        num = Polynomial.QQXs.scalar_mul (QQ.inverse (QQ.abs c)) (RationalTerm.num rt) }
  in
  RationalTerm.term_of ctx result

let simplify_terms_rewriter srk =
  let ctx = RationalTerm.mk_context srk in
  fun expr ->
    match destruct srk expr with
    | `Atom (op, s, t) ->
      let open RationalTerm in
      let rf = (* s - t, as a rational function *)
        let rf =
          of_term ctx (mk_sub srk s t)
        in
        let c = QQXs.content (num rf) in
        if QQ.equal c QQ.zero then
          rf
        else
          { rf with
            num = Polynomial.QQXs.scalar_mul (QQ.inverse (QQ.abs c)) (RationalTerm.num rf) }
      in
      let num_term =
        let denominator =
          BatEnum.fold (fun d (coeff, _) ->
              ZZ.lcm d (QQ.denominator coeff))
            ZZ.one
            (QQXs.enum (num rf))
        in
        QQXs.scalar_mul (QQ.of_zz denominator) (num rf)
        |> QQXs.term_of srk ctx.of_int
      in
      let den_term = Monomial.term_of srk ctx.of_int (den rf) in

      let zero = mk_real srk QQ.zero in
      let result = match op with
        | `Leq ->
          mk_or srk [mk_and srk [mk_leq srk num_term zero; mk_lt srk zero den_term];
                     mk_and srk [mk_leq srk zero num_term; mk_lt srk den_term zero]]
        | `Lt ->
          mk_or srk [mk_and srk [mk_lt srk num_term zero; mk_lt srk zero den_term];
                     mk_and srk [mk_lt srk zero num_term; mk_lt srk den_term zero]]
        | `Eq ->
          mk_and srk [mk_eq srk num_term zero;
                      mk_or srk [mk_lt srk zero den_term; mk_lt srk den_term zero]]

      in
      (result :> ('a,typ_fo) expr)
    | _ -> expr

let simplify_terms srk expr =
  rewrite srk ~up:(simplify_terms_rewriter srk) expr

let purify_rewriter srk table =
  fun expr ->
    match destruct srk expr with
    | `Quantify (_, _, _, _) -> invalid_arg "purify: free variable"
    | `App (_, []) -> expr
    | `App (_, _) ->
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

let simplify_conjunction srk cube =
  let cube = List.map (simplify_terms srk) cube in
  let solver = SrkZ3.mk_solver srk in
  let indicator_map =
    List.fold_left (fun m prop ->
        Symbol.Map.add (mk_symbol srk `TyBool) prop m)
      Symbol.Map.empty
      cube
  in
  SrkZ3.Solver.add solver [mk_not srk (mk_and srk cube)];
  Symbol.Map.iter (fun indicator prop ->
      SrkZ3.Solver.add solver [mk_if srk (mk_const srk indicator) prop])
    indicator_map;
  let assumptions =
    Symbol.Map.fold
      (fun indicator _ xs -> (mk_const srk indicator)::xs)
      indicator_map
      []
  in
  match SrkZ3.Solver.get_unsat_core solver assumptions with
  | `Sat -> assert false
  | `Unknown -> cube
  | `Unsat core ->
    List.map (fun ind ->
        match Formula.destruct srk ind with
        | `Proposition (`App (sym, [])) -> Symbol.Map.find sym indicator_map
        | _ -> assert false)
      core

exception Nonlinear (* not exported *)
let isolate_linear srk x term =
  let rec go term =
    match Term.destruct srk term with
    | `Real k -> `Real k
    | `App (sym, []) when sym = x -> `Lin (QQ.one, [])
    | `Add xs ->
      List.fold_left (fun s t ->
          match s, (go t) with
          | (`Real k, `Real k') -> `Real (QQ.add k k')
          | (`Real k, `Lin (a, b))
          | (`Lin (a, b), `Real k) -> `Lin (a, (mk_real srk k)::b)
          | (`Lin (a, b), `Lin (a', b')) ->
            `Lin (QQ.add a a', b@b'))
        (`Real QQ.zero)
        xs
    | `Mul xs ->
      List.fold_left (fun s t ->
          match s, (go t) with
          | (`Real k, `Real k') -> `Real (QQ.mul k k')
          | (`Real k, _) when QQ.equal k QQ.zero -> `Real QQ.zero
          | (_, `Real k) when QQ.equal k QQ.zero -> `Real QQ.zero
          | (`Real k, `Lin (a, b)) | (`Lin (a, b), `Real k) ->
            `Lin (QQ.mul a k, [mk_mul srk [mk_real srk k; mk_add srk b]])
          | (`Lin (_, _), `Lin (_, _)) -> raise Nonlinear)
        (`Real QQ.one)
        xs
    | `Binop (`Div, s, t) ->
      begin match go s, go t with
        | (`Real k, `Real k') when not (QQ.equal k' QQ.zero) ->
          `Real (QQ.div k k')
        | (`Lin (a, b), `Real k) when not (QQ.equal k QQ.zero) ->
          `Lin (QQ.div a k, [mk_div srk (mk_add srk b) (mk_real srk k)])
        | _ ->
          if Symbol.Set.mem x (symbols term) then
            raise Nonlinear
          else
            `Lin (QQ.zero, [term])
      end
    | `Unop (`Neg, t) ->
      begin match go t with
        | `Real k -> `Real (QQ.negate k)
        | `Lin (a, b) -> `Lin (QQ.negate a, [mk_neg srk (mk_add srk b)])
      end
    | _ ->
      if Symbol.Set.mem x (symbols term) then
        raise Nonlinear
      else
        `Lin (QQ.zero, [term])
  in
  try
    (match go term with
     | `Lin (a, b) -> Some (a, mk_add srk b)
     | `Real k -> Some (QQ.zero, mk_real srk k))
  with Nonlinear -> None

let simplify_dda srk phi =
  let solver = Smt.mk_solver srk in
  let rec simplify_children star children =
    let changed = ref false in
    let rec go simplified = function
      | [] -> List.rev simplified
      | (phi::phis) ->
        Smt.Solver.push solver;
        Smt.Solver.add solver (List.map star simplified);
        Smt.Solver.add solver (List.map star phis);
        let simple_phi = simplify_dda_impl phi in
        Smt.Solver.pop solver 1;
        if not (Formula.equal phi simple_phi) then changed := true;
        go (simple_phi::simplified) phis
    in
    let rec fix children =
      let simplified = go [] children in
      if !changed then begin
        changed := false;
        fix simplified
      end else simplified
    in
    fix children

  and simplify_dda_impl phi =
    match Formula.destruct srk phi with
    | `Or xs -> mk_or srk (simplify_children (mk_not srk) xs)
    | `And xs -> mk_and srk (simplify_children (fun x -> x) xs)
    | _ ->
      Smt.Solver.push solver;
      Smt.Solver.add solver [phi];
      let simplified =
        match Smt.Solver.check solver [] with
        | `Unknown -> phi
        | `Unsat -> mk_false srk
        | `Sat ->
          Smt.Solver.pop solver 1;
          Smt.Solver.push solver;
          Smt.Solver.add solver [mk_not srk phi];
          match Smt.Solver.check solver [] with
          | `Unknown -> phi
          | `Unsat -> mk_true srk
          | `Sat -> phi
      in
      Smt.Solver.pop solver 1;
      simplified
  in
  simplify_dda_impl phi

(* Given a term of the form floor(x/d) with d a positive int, retrieve the pair (x,d) *)
let destruct_idiv srk t =
  match Term.destruct srk t with
  | `Unop (`Floor, t) -> begin match Term.destruct srk t with
      | `Binop (`Div, num, den) -> begin match Term.destruct srk den with
          | `Real den -> begin match QQ.to_int den with
              | Some den when den > 0 -> Some (num, den)
              | _ -> None
            end
          | _ -> None
        end
      | _ -> None
    end
  | _ -> None

let idiv_to_ite srk expr =
  match Expr.refine srk expr with
  | `Term t -> begin match destruct_idiv srk t with
      | Some (num, den) when den < 10 ->
        let den_term = mk_real srk (QQ.of_int den) in
        let num_over_den =
          mk_mul srk [mk_real srk (QQ.of_frac 1 den); num]
        in
        let offset =
          BatEnum.fold (fun else_ r ->
              let remainder_is_r =
                mk_eq srk
                  (mk_mod srk (mk_sub srk num (mk_real srk (QQ.of_int r))) den_term)
                  (mk_real srk QQ.zero)
              in
              mk_ite srk
                remainder_is_r
                (mk_real srk (QQ.of_frac (-r) den))
                else_)
            (mk_real srk QQ.zero)
            (1 -- (den-1))
        in
        (mk_add srk [num_over_den; offset] :> ('a,typ_fo) expr)
      | _ -> expr
    end
  | _ -> expr

let purify_floor srk formula = 
  let f = rewrite srk ~up:(idiv_to_ite srk) formula in
  let g = eliminate_ite srk f in
  let rewriter expr =
    match Expr.refine srk expr with
    | `Term tt -> 
      begin 
        match Term.destruct srk tt with
          | `Unop (`Floor, t) -> (t :> ('a,typ_fo) expr)
          | _ -> expr
      end
    | _ -> expr
  in
  rewrite srk ~up:rewriter g


  let simplify_integer_atom srk op s t =
    let zero = mk_real srk QQ.zero in
    let destruct_int term =
      match Term.destruct srk term with
      | `Real q ->
        begin match QQ.to_zz q with
          | Some z -> z
          | None -> invalid_arg "simplify_atom: non-integral value"
        end
      | _ -> invalid_arg "simplify_atom: non-constant"
    in
    let (s, op) =
      let s =
        if Term.equal t zero then s
        else mk_sub srk s t
      in
      match op with
      | `Lt when (expr_typ srk s = `TyInt) ->
        (simplify_term srk (mk_add srk [s; mk_real srk QQ.one]), `Leq)
      | _ -> (simplify_term srk s, op)
    in
    (* Scale a linterm with rational coefficients so that all coefficients are
       integral *)
    let zz_linterm term =
      let qq_linterm = Linear.linterm_of srk term in
      let multiplier = 
        BatEnum.fold (fun multiplier (qq, _) ->
            ZZ.lcm (QQ.denominator qq) multiplier)
          ZZ.one
          (Linear.QQVector.enum qq_linterm)
      in
      (multiplier, Linear.QQVector.scalar_mul (QQ.of_zz multiplier) qq_linterm)
    in
    match op with
    | `Eq | `Leq ->
      begin match Term.destruct srk s with
      | `Binop (`Mod, dividend, modulus) ->
        (* Divisibility constraint *)
        let modulus = destruct_int modulus in
        let (multiplier, lt) = zz_linterm dividend in
        `Divides (ZZ.mul multiplier modulus, lt)
      | `Unop (`Neg, s') ->
        begin match Term.destruct srk s' with
          | `Binop (`Mod, dividend, modulus) ->
            if op = `Leq then
              (* trivial *)
              `CompareZero (`Leq, Linear.QQVector.zero)
            else
              (* Divisibility constraint *)
              let modulus = destruct_int modulus in
              let (multiplier, lt) = zz_linterm dividend in
              `Divides (ZZ.mul multiplier modulus, lt)
          | _ -> `CompareZero (op, snd (zz_linterm s))
        end
      | `Add [x; y] ->
        begin match Term.destruct srk x, Term.destruct srk y with
          | `Real k, `Binop (`Mod, dividend, modulus)
          | `Binop (`Mod, dividend, modulus), `Real k when QQ.lt k QQ.zero && op = `Eq ->
            let (multiplier, lt) = zz_linterm dividend in
            let modulus = destruct_int modulus in
            if ZZ.equal multiplier ZZ.one && QQ.lt k (QQ.of_zz modulus) then
              let lt = Linear.QQVector.add_term k Linear.const_dim lt in
              `Divides (modulus, lt)
            else
              `CompareZero (op, snd (zz_linterm s))
          | `Binop (`Mod, dividend, modulus), `Real k when QQ.equal QQ.one k && op = `Leq ->
            let (multiplier, lt) = zz_linterm dividend in
            let modulus = destruct_int modulus in
            if ZZ.equal multiplier ZZ.one then
              `NotDivides (modulus, lt)
            else
              `CompareZero (op, snd (zz_linterm s))
          | `Real k, `Unop (`Neg, z) | `Unop (`Neg, z), `Real k when QQ.equal k QQ.one ->
            begin match Term.destruct srk z with
              | `Binop (`Mod, dividend, modulus) ->
                let modulus = destruct_int modulus in
                let (multiplier, lt) = zz_linterm dividend in
                `NotDivides (ZZ.mul multiplier modulus, lt)
              | _ -> `CompareZero (op, snd (zz_linterm s))
            end
          | _, _ -> `CompareZero (op, snd (zz_linterm s))
        end
      | _ -> `CompareZero (op, snd (zz_linterm s))
      end
    | `Lt ->
      begin match Term.destruct srk s with
        | `Binop (`Mod, dividend, modulus) ->
          (* Indivisibility constraint: dividend % modulus < 0. *)
          let modulus = destruct_int modulus in
          let (multiplier, lt) = zz_linterm dividend in
          `NotDivides (ZZ.mul multiplier modulus, lt)
  
        | `Unop (`Neg, s') ->
          begin match Term.destruct srk s' with
            | `Binop (`Mod, dividend, modulus) ->
              (* Indivisibility constraint: dividend % modulus > 0 *)
              let modulus = destruct_int modulus in
              let (multiplier, lt) = zz_linterm dividend in
              `NotDivides (ZZ.mul multiplier modulus, lt)
            | _ -> `CompareZero (`Lt, snd (zz_linterm s))
          end

        | _ -> `CompareZero (`Lt, snd (zz_linterm s))
      end

