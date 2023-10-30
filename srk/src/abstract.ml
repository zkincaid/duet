open Syntax
open Linear
open BatPervasives

include Log.Make(struct let name = "srk.abstract" end)

module V = Linear.QQVector
module CS = CoordinateSystem
module LM = Linear.MakeLinearMap(QQ)(SrkUtil.Int)(V)(V)
module QQXs = Polynomial.QQXs
module I = Polynomial.Rewrite
module Monomial = Polynomial.Monomial

let _pp_numeric_dim base formatter i =
  Format.fprintf formatter "%s_{%d}" base i

module QQXsSpace =
  Linear.MakeLinearSpace
    (QQ)
    (Monomial)
    (struct
      include QQXs
      let split_leading p =
        if QQXs.is_zero p then
          None
        else
          let (coeff, m, rest) = QQXs.split_leading Monomial.degrevlex p in
          Some (m, coeff, rest)
      let pp = QQXs.pp (_pp_numeric_dim "x")
    end)


let opt_abstract_limit = ref (-1)

let boxify srk phi terms =
  let mk_box t ivl =
    let lower =
      match Interval.lower ivl with
      | Some lo -> [mk_leq srk (mk_real srk lo) t]
      | None -> []
    in
    let upper =
      match Interval.upper ivl with
      | Some hi -> [mk_leq srk t (mk_real srk hi)]
      | None -> []
    in
    lower@upper
  in
  match SrkZ3.optimize_box srk phi terms with
  | `Sat intervals ->
    mk_and srk (List.concat (List.map2 mk_box terms intervals))
  | `Unsat -> mk_false srk
  | `Unknown -> assert false

let abstract ?exists:(p=fun _ -> true) srk man phi =
  let module Solver = Smt.StdSolver in
  let solver = Solver.make srk in
  let phi_symbols = symbols phi in
  let symbol_list = Symbol.Set.elements phi_symbols in
  let env_proj = SrkApron.Env.of_set srk (Symbol.Set.filter p phi_symbols) in
  let cs = CoordinateSystem.mk_empty srk in

  let disjuncts = ref 0 in
  let rec go prop =
    Solver.add solver [mk_not srk (SrkApron.formula_of_property prop)];
    let result =
      Log.time "lazy_dnf/sat" (Solver.get_concrete_model solver) symbol_list
    in
    match result with
    | `Unsat -> prop
    | `Unknown ->
      begin
        logf ~level:`warn "abstraction timed out (%d disjuncts); returning top"
          (!disjuncts);
        SrkApron.top man env_proj
      end
    | `Sat interp -> begin
        incr disjuncts;
        logf "[%d] abstract lazy_dnf" (!disjuncts);
        if (!disjuncts) = (!opt_abstract_limit) then begin
          logf ~level:`warn "Met symbolic abstraction limit; returning top";
          SrkApron.top man env_proj
        end else begin
          let disjunct =
            match Interpretation.select_implicant interp phi with
            | Some d -> Polyhedron.of_implicant ~admit:true cs d
            | None -> assert false
          in

          let valuation =
            let table : QQ.t array =
              Array.init (CS.dim cs) (fun i ->
                  Interpretation.evaluate_term
                    interp
                    (CS.term_of_coordinate cs i))
            in
            fun i -> table.(i)
          in
          let projected_coordinates =
            BatEnum.filter (fun i ->
                match CS.destruct_coordinate cs i with
                | `App (sym, _) -> not (p sym)
                | _ -> true)
              (0 -- (CS.dim cs - 1))
            |> BatList.of_enum
          in
          let projected_disjunct =
            Polyhedron.local_project valuation projected_coordinates disjunct
            |> Polyhedron.to_apron cs env_proj man
          in
          go (SrkApron.join prop projected_disjunct)
        end
      end
  in
  Solver.add solver [phi];
  Log.time "Abstraction" go (SrkApron.bottom man env_proj)

type 'a smt_model =
  [ `LIRA of 'a Interpretation.interpretation
  | `LIRR of LirrSolver.Model.t ]

type ('a, 'b) domain =
  { join : 'b -> 'b -> 'b
  ; of_model : 'a smt_model -> 'b
  ; formula_of : 'b -> 'a formula
  ; top : 'b
  ; bottom : 'b }

module Solver = struct
  type 'a smt_solver =
    [ `LIRA of 'a Smt.StdSolver.t
    | `LIRR of 'a LirrSolver.Solver.t ]

  type 'a t =
    { solver : 'a smt_solver
    ; context : 'a context
    ; formula : 'a formula
    ; mutable models : 'a smt_model list }

  let make srk ?(theory=get_theory srk) formula =
    let solver =
      match theory with
      | `LIRR ->
        let s = LirrSolver.Solver.make srk in
        LirrSolver.Solver.add s [formula];
        `LIRR s
      | `LIRA ->
        let s = Smt.StdSolver.make srk in
        Smt.StdSolver.add s [formula];
        `LIRA s
    in
    { solver = solver
    ; models = []
    ; formula = formula
    ; context = srk }

  let get_formula solver = solver.formula
  let get_context solver = solver.context

  let with_blocking s f x =
    match s.solver with
    | `LIRA s ->
      Smt.StdSolver.push s;
      let result = f x in
      Smt.StdSolver.pop s 1;
      result
    | `LIRR s ->
      LirrSolver.Solver.push s;
      let result = f x in
      LirrSolver.Solver.pop s 1;
      result

  let block s phi =
    let not_phi = mk_not (get_context s) phi in
    match s.solver with
    | `LIRA s -> Smt.StdSolver.add s [not_phi]
    | `LIRR s -> LirrSolver.Solver.add s [not_phi]

  let get_model s =
    match s.solver with
    | `LIRA smt_solver ->
      begin match Smt.StdSolver.get_model smt_solver with
        | `Unsat -> `Unsat
        | `Unknown -> `Unknown
        | `Sat m ->
          s.models <- (`LIRA m)::s.models;
          `Sat (`LIRA m)
      end
    | `LIRR smt_solver ->
      begin match LirrSolver.Solver.get_model smt_solver with
        | `Unsat -> `Unsat
        | `Unknown -> `Unknown
        | `Sat m ->
          s.models <- (`LIRR m)::s.models;
          `Sat (`LIRR m)
      end

  let abstract solver domain =
    let rec fix prop =
      block solver (domain.formula_of prop);
      match get_model solver with
      | `Sat m -> fix (domain.join (domain.of_model m) prop)
      | `Unsat -> prop
      | `Unknown -> domain.top
    in
    let init =
      List.fold_left
        (fun a m -> domain.join a (domain.of_model m))
        domain.bottom
        solver.models
    in
    with_blocking solver fix init
end


module Sign = struct

  type sign = Zero | NonNeg | Neg | NonPos | Pos  | Top

  module M = Expr.Map
  type 'a t =
    | Env of ('a, typ_arith, sign) M.t
    | Bottom

  let formula_of srk signs =
    let zero = mk_real srk QQ.zero in
    match signs with
    | Bottom -> mk_false srk
    | Env map ->
      M.fold (fun term sign xs ->
          let term_sign =
            match sign with
            | Pos -> if ArithTerm.typ srk term = `TyInt then
                mk_leq srk (mk_one srk) term
              else
                mk_lt srk zero term
            | Neg -> if ArithTerm.typ srk term = `TyInt then
                mk_leq srk term (mk_neg srk (mk_one srk))
              else
                mk_lt srk term zero
            | Zero -> mk_eq srk term zero
            | NonNeg -> mk_leq srk zero term
            | NonPos -> mk_leq srk term zero
            | Top -> mk_true srk
          in
          term_sign::xs)
        map
        []
      |> mk_and srk

  let join x y =
    let join_sign x y =
      match x, y with
      | Zero, Zero -> Zero

      | Zero, NonNeg | NonNeg, Zero
      | Zero, Pos | Pos, Zero
      | Pos, NonNeg | NonNeg, Pos
      | NonNeg, NonNeg ->
        NonNeg

      | Pos, Pos -> Pos

      | Zero, NonPos | NonPos, Zero
      | Zero, Neg | Neg, Zero
      | Neg, NonPos | NonPos, Neg
      | NonPos, NonPos ->
        NonPos

      | Neg, Neg -> Neg

      | Neg, Pos | Pos, Neg
      | NonNeg, NonPos | NonPos, NonNeg -> Top
      | _, Top | Top, _ -> Top
      | Neg, NonNeg | NonNeg, Neg
      | Pos, NonPos | NonPos, Pos -> Top
    in
    match x, y with
    | Env x, Env y ->
      Env (M.merge (fun _ x y -> match x, y with
          | Some x, Some y -> Some (join_sign x y)
          | _, _ -> Some Top) x y)
    | Bottom, r | r, Bottom -> r

  let equal x y = match x, y with
    | Env x, Env y -> M.equal (=) x y
    | Bottom, Bottom -> true
    | _, _ -> false

  let of_model srk terms m =
    let get_sign term = match m with
      | `LIRR m ->
        begin match LirrSolver.Model.sign srk m term with
          | `Zero -> Zero
          | `Pos -> Pos
          | `Neg -> Neg
          | `Unknown -> Top
        end
      | `LIRA m ->
        let term_val = Interpretation.evaluate_term m term in
        begin match QQ.compare term_val QQ.zero with
          | 0 -> Zero
          | cmp -> if cmp > 0 then Pos else Neg
        end
    in
    let env =
      List.fold_left (fun env t ->
          M.add t (get_sign t) env)
        M.empty
        terms
    in
    Env env

  let top = Env M.empty

  let bottom = Bottom

  let exists p signs = match signs with
    | Bottom -> Bottom
    | Env m ->
       Env (M.filter (fun term _ -> Symbol.Set.for_all p (symbols term)) m)

  let abstract solver ?(bottom=bottom) terms =
    let srk = Solver.get_context solver in
    let formula_of = formula_of srk in
    let of_model = of_model srk terms in
    let domain =
      { join; of_model; formula_of; top; bottom }
    in
    Solver.abstract solver domain
end

module PredicateAbs = struct
  type 'a t = ('a, typ_bool) Expr.Set.t

  let exists p abs_state =
    Expr.Set.filter (fun predicate ->
        Symbol.Set.for_all p (symbols predicate))
      abs_state

  let top = Expr.Set.empty

  let join = Expr.Set.inter

  let equal = Expr.Set.equal

  let formula_of srk abs_state = mk_and srk (Expr.Set.elements abs_state)

  let abstract solver bottom =
    let srk = Solver.get_context solver in
    let of_model m =
      let sat = match m with
        | `LIRR m -> (fun p -> LirrSolver.Model.evaluate_formula srk m p)
        | `LIRA m -> (fun p -> Interpretation.evaluate_formula m p)
      in
      Expr.Set.filter sat bottom
    in
    let formula_of = formula_of srk in
    let domain =
      { join; top; of_model; bottom; formula_of }
    in
    Solver.abstract solver domain
end

module LinearSpan = struct
  type t = Linear.QQVectorSpace.t

  (* Counter-example based extraction of the subspace of the function space
     generated by [terms] that vanishes on the models of phi.  This works by
     repeatedly posing new (linearly independent) functions; each function
     either vanishes on the formula (and gets added to the vanishing space) or
     there is a counter-model on which the function does not vanish.
     Counter-models are collectied in a system of linear equations where the
     variables are the coefficients of candidate functions. *)
  let _abstract_lira solver bottom terms =
    let open Solver in
    let smt_solver =
      match solver.solver with
      | `LIRA s -> s
      | _ -> assert false
    in
    let srk = solver.context in
    let zero = mk_zero srk in
    let next_row =
      let n = ref (-1) in
      fun () -> incr n; (!n)
    in
    let lira_model m =
      match m with
      | `LIRA m -> m
      | _ -> assert false
    in
    let mat =
      List.fold_left (fun mat m ->
          let m = lira_model m in
          let row_num = next_row () in
          let point_row =
            BatArray.fold_lefti (fun row i t ->
                QQVector.add_term (Interpretation.evaluate_term m t) i row)
              QQVector.zero
              terms
          in
          QQMatrix.add_row row_num point_row mat)
        QQMatrix.zero
        solver.models
    in
    let dims = BatList.of_enum (0 -- (Array.length terms - 1)) in
    let mat =
      let bottom_mat =
        QQMatrix.of_rows bottom
      in
      let points = Linear.nullspace bottom_mat dims in
      List.fold_left (fun mat point ->
          let row_num = next_row () in
          QQMatrix.add_row row_num point mat)
        mat
        points
    in
    let rec go vanishing_fns mat dim =
      if dim < 0 then
        vanishing_fns
      else
        let row_num = next_row () in
        (* Find a candidate function which vanishes on all previously
           sampled points *)
        let mat' = QQMatrix.add_row row_num (QQVector.of_term QQ.one dim) mat in
        match Linear.solve mat' (QQVector.of_term QQ.one row_num) with
        | None -> go vanishing_fns mat (dim - 1)
        | Some candidate ->
          Smt.StdSolver.push smt_solver;
          let candidate_term =
            Linear.term_of_vec srk (fun i -> terms.(i)) candidate
          in
          Smt.StdSolver.add smt_solver [
            mk_not srk (mk_eq srk candidate_term zero)
          ];
          match Smt.StdSolver.get_model smt_solver with
          | `Unknown -> (* give up; return the functions we have so far *)
            Smt.StdSolver.pop smt_solver 1;
            logf ~level:`warn
              "vanishing_space timed out (%d functions)"
              (List.length vanishing_fns);
            vanishing_fns
          | `Unsat -> (* candidate vanishes on phi *)
            Smt.StdSolver.pop smt_solver 1;
            go (candidate::vanishing_fns) mat' (dim - 1)
          | `Sat point -> (* candidate is non-zero at point *)
            Smt.StdSolver.pop smt_solver 1;
            let point_row =
              BatArray.fold_lefti (fun row i t ->
                  QQVector.add_term (Interpretation.evaluate_term point t) i row)
                QQVector.zero
                terms
            in
            solver.models <- (`LIRA point)::solver.models;
            let mat' = QQMatrix.add_row row_num point_row mat in
            (* We never choose the same candidate function again,
               because the only solutions to the system of equations
               mat' x = 0 are functions that vanish on all samples *)
            go vanishing_fns mat' dim
  in
  go [] mat (Array.length terms - 1)

  let _abstract_lirr solver bottom terms =
    let srk = Solver.(solver.context) in
    let poly_terms = Array.map (QQXs.of_term srk) terms in
    let dim = Array.length terms in
    let of_model m =
      match m with
      | `LIRA _ -> assert false
      | `LIRR m ->
        let ideal = PolynomialCone.get_ideal (LirrSolver.Model.nonnegative_cone m) in
        Log.error ">> %a" (I.pp (_pp_numeric_dim "x")) ideal;
        let shift =
          QQXs.substitute (fun i ->
              let i' = if i > 0 then i + dim else i in
              QQXs.of_dim i')
        in
        let reduced =
          BatArray.fold_lefti (fun space i t ->
              let t_sub_reduced =
                QQXs.add_term
                  (QQ.of_int (-1))
                  (Monomial.singleton i 1)
                  (shift (I.reduce ideal t))
              in
              QQXsSpace.add t_sub_reduced space)
            QQXsSpace.zero
            poly_terms
        in
        let standard_basis =
          BatArray.fold_lefti (fun space i _ ->
              QQXsSpace.add
                (QQXs.add_term QQ.one (Monomial.singleton i 1) QQXs.zero)
                space)
            QQXsSpace.zero
            terms
        in
        QQXsSpace.intersect reduced standard_basis
        |> QQXsSpace.basis
        |> BatEnum.map (fun p -> match QQXs.vec_of p with
            | Some v -> v
            | None -> assert false)
        |> BatList.of_enum
    in
    let join = Linear.QQVectorSpace.intersect in
    let top = [] in
    let zero = mk_zero srk in
    let formula_of relations =
      List.map (fun vec ->
          mk_eq srk (Linear.term_of_vec srk (Array.get terms) vec) zero)
        relations
      |> mk_and srk
    in
    let domain =
      { join; top; of_model; bottom; formula_of }
    in
    Solver.abstract solver domain

  module Int = SrkUtil.Int
  let abstract solver ?(bottom=None) terms =
    let bottom = match bottom with
      | Some v -> v
      | None -> QQVectorSpace.standard_basis (Array.length terms)
    in
    match Solver.(solver.solver) with
    | `LIRR _ -> _abstract_lirr solver bottom terms
    | `LIRA _ -> _abstract_lira solver bottom terms

  let affine_hull solver ?(bottom=[V.of_term QQ.one Linear.const_dim]) symbols =
    let trivial = V.of_term QQ.one Linear.const_dim in
    let srk = Solver.get_context solver in
    let basis =
      BatArray.of_list (mk_one srk :: (List.map (mk_const srk) symbols))
    in
    let map =
      BatList.fold_lefti (fun map i sym ->
          Int.Map.add (int_of_symbol sym) (i + 1) map)
        (Int.Map.singleton Linear.const_dim 0)
        symbols
    in
    let subst = BatArray.map (Linear.linterm_of srk) basis in
    let project keep relations =
      let keep_space =
        Int.Set.fold (fun dim space ->
            (Linear.QQVector.of_term QQ.one dim)::space)
          keep
          []
      in
      Linear.QQVectorSpace.intersect keep_space relations
    in
    let bottom =
      if Linear.QQVectorSpace.mem bottom trivial then
        None
      else
        let keep =
          BatList.fold_left (fun keep sym ->
              Int.Set.add (int_of_symbol sym) keep)
            (Int.Set.singleton Linear.const_dim)
            symbols
        in
        let relations = project keep bottom in
        Some (List.map (fun vec ->
            BatEnum.fold
              (fun vec' (coeff, dim) ->
                 Linear.QQVector.add_term coeff (Int.Map.find dim map) vec')
              Linear.QQVector.zero
              (Linear.QQVector.enum vec))
            relations)
    in
    abstract solver ~bottom basis
    |> List.map (fun vec ->
        BatEnum.fold (fun vec' (coeff, dim) ->
            V.add (V.scalar_mul coeff subst.(dim)) vec')
          V.zero
          (V.enum vec))
end

module ConvexHull = struct
  type t = DD.closed DD.t

  let of_model_lira solver man terms =
    let srk = Solver.get_context solver in
    let phi = Solver.get_formula solver in
    (* Map linear terms over the symbols in phi to the range [-1, n], such that
       -1 -> -1, 0 -> term(0), ... n -> term(n) *)
    let basis = BatDynArray.create () in
    let map =
      let neg_one = V.of_term QQ.one Linear.const_dim in
      BatArray.fold_lefti (fun map i t ->
          let vec = Linear.linterm_of srk t in
          BatDynArray.add basis vec;
          LM.may_add vec (V.of_term QQ.one i) map)
        (LM.add_exn neg_one neg_one LM.empty)
        terms
      |> Symbol.Set.fold (fun symbol map ->
          let symbol_vec = V.of_term QQ.one (Linear.dim_of_sym symbol) in
          let ambient_dim = BatDynArray.length basis in
          match LM.add symbol_vec (V.of_term QQ.one ambient_dim) map with
          | Some map' ->
            BatDynArray.add basis symbol_vec;
            map'
          | None -> map)
        (symbols phi)
    in
    let dim = Array.length terms in
    let elim_dims = BatList.of_enum (dim -- (BatDynArray.length basis)) in
    function
    | `LIRR _ -> assert false
    | `LIRA interp ->
      let cube =
        match Interpretation.select_implicant interp phi with
        | Some cube ->
          let constraints = BatEnum.empty () in
          BatList.iter (fun atom ->
              match Interpretation.destruct_atom srk atom with
              | `ArithComparison (p, x, y) ->
                let t =
                  V.sub (Linear.linterm_of srk y) (Linear.linterm_of srk x)
                  |> LM.apply map
                  |> BatOption.get
                in
                let p = match p with `Eq -> `Zero | `Leq -> `Nonneg | `Lt -> `Pos in
                BatEnum.push constraints (p, t)
              | _ -> ())
            cube;
          Polyhedron.of_constraints constraints
        | None -> assert false
      in
      let valuation i =
        Linear.evaluate_linterm
          (Interpretation.real interp)
          (BatDynArray.get basis i)
      in
      Polyhedron.local_project valuation elim_dims cube
      |> Polyhedron.dd_of ~man dim

  let of_model_lirr solver man terms =
    let srk = Solver.get_context solver in
    let poly_terms = Array.map (QQXs.of_term srk) terms in
    let dim = Array.length terms in
    function
    | `LIRA _ -> assert false
    | `LIRR m ->
      let cone = LirrSolver.Model.nonnegative_cone m in
      let map_cone = PolynomialCone.inverse_image cone poly_terms in
      let constraints = BatEnum.empty () in
      I.generators (PolynomialCone.get_ideal map_cone)
      |> List.iter (fun p ->
          match QQXs.vec_of p with
          | Some vec -> BatEnum.push constraints (`Zero, vec)
          | None -> ());
      PolynomialCone.get_cone_generators map_cone
      |> List.iter (fun p ->
          match QQXs.vec_of p with
          | Some vec -> BatEnum.push constraints (`Nonneg, vec)
          | None -> ());
      DD.of_constraints_closed ~man dim constraints

  let abstract solver ?(man=Polka.manager_alloc_loose ()) ?(bottom=None) terms =
    let join = DD.join in
    let dim = Array.length terms in
    let srk = Solver.get_context solver in
    let top = DD.of_constraints_closed ~man dim (BatEnum.empty ()) in
    let bottom = match bottom with
      | Some bot -> bot
      | None ->
        let inconsistent = (* 0 = 1 *)
          BatEnum.singleton (`Zero, V.of_term QQ.one Linear.const_dim)
        in
        DD.of_constraints_closed ~man dim inconsistent
    in
    let term_of_dim i =
      if i == Linear.const_dim then mk_one srk else terms.(i)
    in
    let formula_of prop =
      DD.enum_constraints_closed prop
      /@ (fun (kind, v) ->
          let t = Linear.term_of_vec srk term_of_dim v in
          match kind with
          | `Zero -> mk_eq srk (mk_zero srk) t
          | `Nonneg -> mk_leq srk (mk_zero srk) t)
      |> BatList.of_enum
      |> mk_and srk
    in
    let of_model = match Solver.(solver.solver) with
      | `LIRA _ -> of_model_lira solver man terms
      | `LIRR _ -> of_model_lirr solver man terms
    in
    let domain =
      { join; top; of_model; bottom; formula_of }
    in
    Solver.abstract solver domain
end

let vanishing_space srk phi terms =
  let solver = Solver.make srk phi in
  LinearSpan.abstract solver terms

let affine_hull srk phi constants =
  let basis =
    BatArray.of_list (mk_one srk :: (List.map (mk_const srk) constants))
  in
  vanishing_space srk phi basis
  |> List.map (Linear.term_of_vec srk (fun i -> basis.(i)))

let conv_hull ?(man=Polka.manager_alloc_loose ()) srk phi terms =
  let solver = Solver.make srk phi in
  ConvexHull.abstract solver ~man terms
