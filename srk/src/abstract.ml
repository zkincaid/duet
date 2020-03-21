open Syntax
open Linear
open BatPervasives

include Log.Make(struct let name = "srk.abstract" end)

module V = Linear.QQVector
module CS = CoordinateSystem

let opt_abstract_limit = ref (-1)

(* Counter-example based extraction of the affine hull of a formula.  This
   works by repeatedly posing new (linearly independent) equations; each
   equation is either implied by the formula (and gets added to the affine
   hull) or there is a counter-example point which shows that it is not.
   Counter-example points are collecting in a system of linear equations where
   the variables are the coefficients of candidate equations. *)
let affine_hull srk phi constants =
  let solver = Smt.mk_solver srk in
  Smt.Solver.add solver [phi];
  let next_row =
    let n = ref (-1) in
    fun () -> incr n; (!n)
  in
  let vec_one = QQVector.of_term QQ.one Linear.const_dim in
  let rec go equalities mat = function
    | [] -> equalities
    | (k::ks) ->
      let dim = dim_of_sym k in
      let row_num = next_row () in
      (* Find a candidate equation which is satisfied by all previously
         sampled points, and where the coefficient of k is 1 *)
      let mat' = QQMatrix.add_row row_num (QQVector.of_term QQ.one dim) mat in
      match Linear.solve mat' (QQVector.of_term QQ.one row_num) with
      | None -> go equalities mat ks
      | Some candidate ->
        Smt.Solver.push solver;
        let candidate_term =
          QQVector.enum candidate
          /@ (fun (coeff, dim) ->
              match sym_of_dim dim with
              | Some const -> mk_mul srk [mk_real srk coeff; mk_const srk const]
              | None -> mk_real srk coeff)
          |> BatList.of_enum
          |> mk_add srk
        in
        Smt.Solver.add solver [
          mk_not srk (mk_eq srk candidate_term (mk_real srk QQ.zero))
        ];
        match Smt.Solver.get_concrete_model solver constants with
        | `Unknown -> (* give up; return the equalities we have so far *)
          logf ~level:`warn
            "Affine hull timed out (%d equations)"
            (List.length equalities);
          equalities
        | `Unsat -> (* candidate equality is implied by phi *)
          Smt.Solver.pop solver 1;
          (* We never choose the same candidate equation again, because the
             system of equations mat' x = 0 implies that the coefficient of k
             is zero *)
          go (candidate_term::equalities) mat' ks
        | `Sat point -> (* candidate equality is not implied by phi *)
          Smt.Solver.pop solver 1;
          let point_row =
            List.fold_left (fun row k ->
                QQVector.add_term
                  (Interpretation.real point k)
                  (dim_of_sym k)
                  row)
              vec_one
              constants
          in
          let mat' = QQMatrix.add_row row_num point_row mat in
          (* We never choose the same candidate equation again, because the
             only solutions to the system of equations mat' x = 0 are
             equations which are satisfied by the sampled point *)
          go equalities mat' (k::ks)
  in
  go [] QQMatrix.zero constants

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

let nb_hulls = ref 0
let dump_hull = ref false
let dump_hull_prefix = ref ""

let abstract ?exists:(p=fun _ -> true) srk man phi =
  let solver = Smt.mk_solver srk in
  let phi_symbols = symbols phi in
  let symbol_list = Symbol.Set.elements phi_symbols in
  let env_proj = SrkApron.Env.of_set srk (Symbol.Set.filter p phi_symbols) in
  let cs = CoordinateSystem.mk_empty srk in

  if !dump_hull then begin
      let query =
        List.fold_left (fun phi s ->
            if p s then
              phi
            else
              mk_exists_const srk s phi)
          phi
          symbol_list
      in
      let filename =
        Format.sprintf "%shull%d.smt2" (!dump_hull_prefix) (!nb_hulls)
      in
      let chan = Stdlib.open_out filename in
      let formatter = Format.formatter_of_out_channel chan in
      logf ~level:`always "Writing convex hull query to %s" filename;
      Syntax.pp_smtlib2 srk formatter query;
      Format.pp_print_newline formatter ();
      Stdlib.close_out chan;
      incr nb_hulls
    end;

  let disjuncts = ref 0 in
  let rec go prop =
    Smt.Solver.push solver;
    Smt.Solver.add solver [mk_not srk (SrkApron.formula_of_property prop)];
    let result =
      Log.time "lazy_dnf/sat" (Smt.Solver.get_concrete_model solver) symbol_list
    in
    match result with
    | `Unsat ->
      Smt.Solver.pop solver 1;
      prop
    | `Unknown ->
      begin
        logf ~level:`warn "abstraction timed out (%d disjuncts); returning top"
          (!disjuncts);
        Smt.Solver.pop solver 1;
        SrkApron.top man env_proj
      end
    | `Sat interp -> begin
        Smt.Solver.pop solver 1;
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
  Smt.Solver.add solver [phi];
  Log.time "Abstraction" go (SrkApron.bottom man env_proj)

module Sign = struct

  type sign = Zero | NonNeg | Neg | NonPos | Pos  | Top

  type t =
    | Env of sign Symbol.Map.t
    | Bottom

  let formula_of srk signs =
    let zero = mk_real srk QQ.zero in
    match signs with
    | Bottom -> mk_false srk
    | Env map ->
      Symbol.Map.fold (fun sym sign xs ->
          let sym_sign =
            match sign with
            | Pos -> mk_lt srk zero (mk_const srk sym)
            | Neg -> mk_lt srk (mk_const srk sym) zero
            | Zero -> mk_eq srk (mk_const srk sym) zero
            | NonNeg -> mk_leq srk zero (mk_const srk sym)
            | NonPos -> mk_leq srk (mk_const srk sym) zero
            | Top -> mk_true srk
          in
          sym_sign::xs)
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
      Env (Symbol.Map.merge (fun _ x y -> match x, y with
          | Some x, Some y -> Some (join_sign x y)
          | _, _ -> Some Top) x y)
    | Bottom, r | r, Bottom -> r

  let equal x y = match x, y with
    | Env x, Env y -> Symbol.Map.equal (=) x y
    | Bottom, Bottom -> true
    | _, _ -> false

  let of_model m symbols =
    let rational_sign x =
      match QQ.compare x QQ.zero with
      | 0 -> Zero
      | c when c < 0 -> Neg
      | _ -> Pos
    in
    let env =
      List.fold_left (fun env sym ->
          Symbol.Map.add sym (rational_sign (Interpretation.real m sym)) env)
        Symbol.Map.empty
        symbols
    in
    Env env

  let top = Env Symbol.Map.empty

  let bottom = Bottom

  let exists p signs = match signs with
    | Bottom -> Bottom
    | Env m ->
      Env (Symbol.Map.mapi (fun sym sign -> if p sym then sign else Top) m)
end

module MakeAbstractRSY (C : sig
    type t
    val context : t context
  end) = struct

  module type Domain = sig
    type t
    val top : t
    val bottom : t
    val exists : (symbol -> bool) -> t -> t
    val join : t -> t -> t
    val equal : t -> t -> bool
    val of_model : C.t Interpretation.interpretation -> symbol list -> t
    val formula_of : t -> C.t formula
  end

  module Sign = struct
    include Sign
    let formula_of = formula_of C.context
  end

  module AffineRelation = struct
    type t = (C.t, Polka.equalities Polka.t) SrkApron.property

    let man = Polka.manager_alloc_equalities ()

    let top = SrkApron.top man (SrkApron.Env.of_list C.context [])
    let bottom = SrkApron.bottom man (SrkApron.Env.empty C.context)

    let of_model m symbols =
      let env = SrkApron.Env.of_list C.context symbols in
      List.map (fun sym ->
          Linear.QQVector.add_term
            (QQ.of_int (-1))
            (Linear.dim_of_sym sym)
            (Linear.const_linterm (Interpretation.real m sym))
          |> SrkApron.lexpr_of_vec env
          |> SrkApron.lcons_eqz
        ) symbols
      |> SrkApron.meet_lcons (SrkApron.top man env)

    let exists p prop = SrkApron.exists man p prop
    let join = SrkApron.join
    let equal = SrkApron.equal
    let formula_of = SrkApron.formula_of_property
  end

  module PredicateAbs (U : sig val universe : C.t formula list end) = struct
    module PS = struct
      include BatSet.Make(struct
          type t = C.t formula
          let compare = Formula.compare
        end)
    end

    type t = PS.t

    let universe = PS.of_list U.universe

    let exists p abs_state =
      PS.filter (fun predicate ->
          Symbol.Set.for_all p (symbols predicate))
        abs_state
    let top = PS.empty
    let bottom = universe
    let join = PS.inter
    let equal = PS.equal
    let of_model m _ = PS.filter (Interpretation.evaluate_formula m) universe
    let formula_of abs_state = mk_and C.context (PS.elements abs_state)
  end

  module Product (A : Domain) (B : Domain) = struct
    type t = A.t * B.t
    let top = (A.top, B.top)
    let bottom = (A.bottom, B.bottom)
    let exists p (v1, v2) = (A.exists p v1, B.exists p v2)
    let join (v1, v2) (v1', v2') = (A.join v1 v1', B.join v2 v2')
    let equal (v1, v2) (v1', v2') = A.equal v1 v1' && B.equal v2 v2'
    let of_model  m symbols = (A.of_model m symbols, B.of_model m symbols)
    let formula_of  (v1, v2) = mk_and C.context [A.formula_of v1; B.formula_of v2]
  end

  let abstract (type a)
      ?exists:(p=fun _ -> true)
      (module D : Domain with type t = a)
      phi =
    let phi_symbols = Symbol.Set.filter p (symbols phi) |> Symbol.Set.elements in
    let solver = Smt.mk_solver C.context in
    Smt.Solver.add solver [phi];
    let rec fix prop =
      Smt.Solver.add solver [mk_not C.context (D.formula_of prop)];
      match Smt.Solver.get_model solver with
      | `Sat m ->
        fix (D.join (D.of_model m phi_symbols) prop)
      | `Unsat -> prop
      | `Unknown ->
        logf ~level:`warn "Unknown result in MakeAbstractRSY.abstract";
        D.top
    in
    fix D.bottom

end
