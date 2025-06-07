open Syntax
module P = Polyhedron
module L = IntLattice

module V = Linear.QQVector

include Log.Make (struct let name = "srk.polyhedronLatticeTiling" end)

let () = my_verbosity_level := `info
let test_convex_hull = ref false
let test_level = ref `debug

let eager_hermite = ref false

module LocalAbstraction : sig

  (** A concept space consists of a representation of points
      and a representation of concepts (sets of points).

      For concept spaces C_i = ('concept_i, 'point_i), i = 1, 2,
      a function [f: 'concept_1 -> 'concept_2] is called a universe translation.
      A local abstraction respecting [f] is a function [abstract]
      such that for all [pt] in [concept],
      [f(pt)] \in [abstract pt concept] \subseteq [f(concept)].

      There are three concept spaces of interest:
      - Formulas and interpretations
      - PLTs (polyhedron-lattice-tiling) and points ([int -> QQ.t])
      - DDs (double-description polyhedra) and points ([int -> QQ.t])
   *)

  type ('concept1, 'point1, 'concept2, 'point2) t =
    {
      abstract: 'point1 -> 'concept1 -> 'concept2
    ; translate: 'point1 -> 'point2
    }

  val compose:
    ('concept2, 'point2, 'concept3, 'point3) t ->
    ('concept1, 'point1, 'concept2, 'point2) t ->
    ('concept1, 'point1, 'concept3, 'point3) t

  (* Requires that the underlying universe translations are the same *)
  val join:
    ('concept2 -> 'concept2 -> 'concept2) ->
    ('concept1, 'point1, 'concept2, 'point2) t ->
    ('concept1, 'point1, 'concept2, 'point2) t ->
    ('concept1, 'point1, 'concept2, 'point2) t

end = struct

  type ('concept1, 'point1, 'concept2, 'point2) t =
    {
      abstract: 'point1 -> 'concept1 -> 'concept2
    ; translate: 'point1 -> 'point2
    }

  let compose
        (t2: ('concept2, 'point2, 'concept3, 'point3) t)
        (t1: ('concept1, 'point1, 'concept2, 'point2) t) =
    let translate p = t2.translate (t1.translate p) in
    let abstract x c = t2.abstract (t1.translate x) (t1.abstract x c) in
    { abstract
    ; translate
    }

  let join concept_join t1 t2 =
    let abstract x c = concept_join (t1.abstract x c) (t2.abstract x c) in
    {
      abstract
    ; translate = t1.translate
    }

end

module IntSet = SrkUtil.Int.Set
module IntMap = SrkUtil.Int.Map

let default_vec_of_sym k = V.of_term QQ.one (Linear.dim_of_sym k)
let default_term_of_dim srk dim =
  match Linear.sym_of_dim dim with
  | Some k -> mk_const srk k
  | None ->
     assert (dim == Linear.const_dim);
     mk_one srk

let term_of_vec srk term_of_dim =
  Linear.term_of_vec srk (fun d ->
      if d = Linear.const_dim then mk_one srk
      else term_of_dim d)

let formula_p srk term_of_dim (kind, v) =
  let t = term_of_vec srk term_of_dim v in
  match kind with
  | `Zero -> mk_eq srk t (mk_zero srk)
  | `Nonneg -> mk_leq srk (mk_zero srk) t
  | `Pos -> mk_lt srk (mk_zero srk) t

let formula_l srk term_of_dim v =
  let t = term_of_vec srk term_of_dim v in
  mk_is_int srk t

let formula_t srk term_of_dim v =
  let t = term_of_vec srk term_of_dim v in
  mk_not srk (mk_is_int srk t)

let formula_of_dd srk term_of_dim dd =
  DD.enum_constraints dd
  |> BatEnum.fold
       (fun atoms (kind, v) -> formula_p srk term_of_dim (kind, v) :: atoms) []
  |> List.rev
  |> mk_and srk

let collect_dimensions vector_of add_dim constraints =
  let dims = ref IntSet.empty in
  BatList.iter
    (fun constr ->
      V.enum (vector_of constr)
      |> BatEnum.iter
           (fun (_, dim) ->
             if dim <> Linear.const_dim && add_dim dim
             then dims := IntSet.add dim !dims
             else ())
    )
    constraints;
  !dims

let pp_dim fmt dim = Format.fprintf fmt "(dim %d)" dim

let pp_vector = V.pp_term pp_dim

let pp_pconstr = Polyhedron.pp_constraint pp_dim

let _pp_term_of_dim srk fmt map =
  IntMap.iter
    (fun dim term ->
      Format.fprintf fmt "(%d: %a), "
        dim
        (Syntax.ArithTerm.pp srk) term)
    map

let log_plt_constraints ~level str (p, l, t) =
  logf ~level
    "%s: p_constraints: @[%a@]@\n" str
    (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "@\n")
       pp_pconstr) p;
  logf ~level
    "%s: l_constraints: @[%a@]@\n" str
    (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "@\n")
       pp_vector) l;
  logf ~level
    "%s: t_constraints: @[%a@]@\n" str
    (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "@\n")
       pp_vector) t

let test_point_in_polyhedron ?(level = !test_level) str m p =
  if Log.level_leq !my_verbosity_level level then
    List.iter
      (fun (kind, v) ->
        logf ~level:!my_verbosity_level "%s: testing @[%a@]" str pp_pconstr (kind, v);
        let result = Linear.evaluate_affine m v in
        match kind with
        | `Zero ->
           if not (QQ.equal result QQ.zero) then
             failwith
               (Format.asprintf "%s: evaluated vector to %a, expected 0"
                  str QQ.pp result)
           else ()
        | `Nonneg -> assert (QQ.leq QQ.zero result)
        | `Pos -> assert (QQ.lt QQ.zero result)
      )
      p
  else ()

let test_point_in_lattice ?(level = !test_level) is_int str m l =
  if Log.level_leq !my_verbosity_level level then
    List.iter
      (fun v ->
        logf ~level:!my_verbosity_level "%s: testing %a(%a)"
          str
          (fun fmt is_int -> match is_int with
                             | `IsInt -> Format.fprintf fmt "Int"
                             | `NotInt -> Format.fprintf fmt "~Int")
          is_int
          Linear.QQVector.pp v;
        let result = Linear.evaluate_affine m v in
        match QQ.to_zz result, is_int with
        | Some _, `IsInt -> ()
        | None, `NotInt -> ()
        | None, `IsInt ->
           failwith
             (Format.asprintf "%s: evaluated vector to %a, expected an integer"
                str QQ.pp result)
        | Some _, `NotInt ->
           failwith
             (Format.asprintf "%s: evaluated vector to %a, expected a non-integer"
                str QQ.pp result)
      )
      l
  else ()

let test_implication ?(level = !test_level) str solver consequence =
  if Log.level_leq !my_verbosity_level level then
    begin
      logf str;
      let srk = Abstract.Solver.get_context solver in
      let phi = Abstract.Solver.get_formula solver in
      let goal = Syntax.mk_and srk [phi; Syntax.mk_not srk consequence] in
      let solver = SrkZ3.Solver.make srk in
      let msg status =
        Format.asprintf "@[%a@]@\n %s @\n@[%a@]@;"
          (Syntax.Formula.pp srk) phi
          status
          (Syntax.Formula.pp srk) consequence
      in
      SrkZ3.Solver.add solver [goal];
      if (SrkZ3.Solver.check solver = `Unsat) then
        logf "Test passed: %s" (msg "implies")
      else
        failwith (msg "does not imply")
    end
  else ()

let _test_hull ?(level = !test_level) solver terms dd =
  if Log.level_leq !my_verbosity_level level && !test_convex_hull then
    let srk = Abstract.Solver.get_context solver in
    let consequence = formula_of_dd srk (fun dim -> terms.(dim)) dd in
    test_implication
      "Checking if convex hull is consistent with input formula..."
      solver consequence
  else
    ()

type plt_constraints = (P.constraint_kind * V.t) list * V.t list * V.t list

module Plt: sig

  (** Concept spaces of PLTs and geometric points.
      A PLT is a polyhedron, lattice, and tiling representing a conjunctive
      formula in linear integer-real arithmetic.
      Formulas should only have linear real arithmetic terms,
      i.e., no floor, mod, non-trivial multiplication and division, etc.
      Formulas with these terms can be purified using [Syntax.eliminate_floor_mod_div] etc.
   *)

  type t

  val formula_of_plt: 'a Syntax.context -> (int -> 'a arith_term) -> t -> 'a formula

  val constrained_dimensions: t -> IntSet.t

  (** [cubify srk terms symbols] is a local abstraction mapping formulas over [symbols]
      to a PLT in a space where dimensions 0, ..., length([terms]) - 1 correspond to
      [terms[0]] to [terms[length(terms) - 1]] and dimensions above that correspond
      to symbols: the dimension for [sym] is [int_of_symbol symbol + length(terms)].

      The local abstraction respects integrality of symbols, i.e., it considers an
      input formula [F] as [F /\ /\_{x} is_int(x)], where [x] ranges over symbols in [F].
   *)
  val cubify:
    'a context -> 'a arith_term array -> Symbol.Set.t ->
    ('a formula, 'a Interpretation.interpretation, t, int -> QQ.t) LocalAbstraction.t
    * (int -> 'a arith_term)

  val poly_part: t -> P.t
  val lattice_part: t -> L.unreduced L.t
  val tiling_part: t -> L.unreduced L.t

  val mk_plt:
    poly_part:P.t ->
    lattice_part: L.unreduced L.t -> tiling_part: L.unreduced L.t -> t

  val plt_constraints_of_cube : 'a context ->
                                (symbol -> V.t) ->
                                'a formula list ->
                                plt_constraints

  val formula_of_plt_constraints: 'a Syntax.context ->
                                  ?term_of_dim:('a context -> int -> 'a arith_term) ->
                                  plt_constraints ->
                                  'a formula

end = struct
  type t =
    {
      poly_part: P.t
    ; lattice_part: L.unreduced L.t
    ; tiling_part: L.unreduced L.t
    }

  let poly_part plt = plt.poly_part
  let lattice_part plt = plt.lattice_part
  let tiling_part plt = plt.tiling_part
  let mk_plt ~poly_part ~lattice_part ~tiling_part =
    {
      poly_part
    ; lattice_part
    ; tiling_part
    }

  let mk_lattice l =
    let lattice = L.of_generators l in
    try
      if !eager_hermite then
        L.hermitize lattice |> L.forget
      else lattice
    with
    | Stack_overflow -> lattice

  let constrained_dimensions plt =
    let p = BatList.of_enum (P.enum_constraints plt.poly_part) in
    let l = L.generators plt.lattice_part in
    let t = L.generators plt.tiling_part in
    collect_dimensions (fun (_, v) -> v) (fun _ -> true) p
    |> IntSet.union (collect_dimensions (fun v -> v) (fun _ -> true) l)
    |> IntSet.union (collect_dimensions (fun v -> v) (fun _ -> true) t)

  type lin_cond =
    {
      p_cond: (P.constraint_kind * V.t) list
    ; l_cond: V.t list
    ; t_cond: V.t list
    }

  let tru =
    {
      p_cond = []
    ; l_cond = []
    ; t_cond = []
    }

  let conjoin lin1 lin2 =
    {
      p_cond = List.rev_append lin1.p_cond lin2.p_cond
    ; l_cond = List.rev_append lin1.l_cond lin2.l_cond
    ; t_cond = List.rev_append lin1.t_cond lin2.t_cond
    }

  let plt_constraint_of_atom srk ?vec_of_sym atom =
    match Linear.destruct_lira_atom srk ?vec_of_sym atom with
    | (`Pos, v) -> { tru with p_cond = [(`Pos, v)] }
    | (`Nonneg, v) -> { tru with p_cond = [(`Nonneg, v)] }
    | (`Zero, v) -> { tru with p_cond = [(`Zero, v)] }
    | (`IsInt, v) -> { tru with l_cond = [v] }
    | (`NotInt, v) -> { tru with t_cond = [v] }

  let integer_symbols srk atoms =
    List.fold_left
      (fun symbols atom ->
        Syntax.Symbol.Set.fold
          (fun sym vectors -> match Syntax.typ_symbol srk sym with
                              | `TyInt -> Syntax.Symbol.Set.add sym symbols
                              | _ -> vectors)
          (Syntax.symbols atom) symbols
      )
      Syntax.Symbol.Set.empty
      atoms

  let plt_implicant_of_implicant srk vec_of_sym atoms =
    let lincond =
      List.fold_left (fun lincond atom ->
          let lincond_atom =
            plt_constraint_of_atom srk ~vec_of_sym atom in
          conjoin lincond_atom lincond
        )
        tru
        atoms
    in
    let integers =
      { p_cond = []
      ; l_cond =
          Syntax.Symbol.Set.elements (integer_symbols srk atoms)
          |> List.map vec_of_sym
      ; t_cond = []
      }
    in
    conjoin lincond integers

  let plt_constraints_of_cube srk vec_of_symbol atoms =
    let constraints = plt_implicant_of_implicant srk vec_of_symbol atoms in
    (constraints.p_cond, constraints.l_cond, constraints.t_cond)

  let formula_of_plt_constraints srk ?(term_of_dim=default_term_of_dim) (p, l, t) =
    let term_of_dim = term_of_dim srk in
    let phis_p = List.map (formula_p srk term_of_dim) p in
    let phis_l = List.map (formula_l srk term_of_dim) l in
    let phis_t = List.map (formula_l srk term_of_dim) t in
    mk_and srk (phis_p @ phis_l @ phis_t)

  let formula_of_plt srk term_of_dim plt =
    let phis_p =
      BatEnum.map (formula_p srk term_of_dim) (P.enum_constraints plt.poly_part)
      |> BatList.of_enum
    in
    let phis_l =
      List.map (formula_l srk term_of_dim) (L.generators plt.lattice_part)
    in
    let phis_t =
      List.map (formula_t srk term_of_dim) (L.generators plt.tiling_part)
    in
    mk_and srk (phis_p @ phis_l @ phis_t)

  let mk_term_definitions srk dim_of_symbol terms =
    let vec_of_sym k = V.of_term QQ.one (dim_of_symbol k) in
    let linearize = Linear.linterm_of srk ~vec_of_sym in
    let vector_of_term idx = V.of_term QQ.one idx in
    let p_conds = ref (BatEnum.empty ()) in
    Array.iteri
      (fun dim term ->
        let v = linearize term in
        BatEnum.push !p_conds (`Zero, V.add v (V.negate (vector_of_term dim)))
      )
      terms;
    BatList.of_enum !p_conds

  let get_max_dim num_terms symbols =
    match Symbol.Set.max_elt_opt symbols with
    | None -> num_terms - 1
    | Some dim -> Syntax.int_of_symbol dim + num_terms

  let implicit_is_ints srk vec_of_symbol conjuncts =
    let typ_int sym = (Syntax.typ_symbol srk sym = `TyInt) in
    let int_symbols =
      List.fold_left
        (fun int_symbols fml ->
          Syntax.symbols fml
          |> Syntax.Symbol.Set.filter typ_int
          |> Syntax.Symbol.Set.union int_symbols
        )
        Syntax.Symbol.Set.empty conjuncts
    in
    Syntax.Symbol.Set.fold
      (fun sym intcond -> vec_of_symbol sym :: intcond)
      int_symbols
      []

  let cubify srk terms symbols =
    let num_terms = Array.length terms in
    let max_dim = get_max_dim num_terms symbols in
    logf ~level:`debug "initial plt abstraction: max_dim: %d, num_terms = %d@;"
      max_dim num_terms;
    let dim_of_symbol sym = Syntax.int_of_symbol sym + num_terms in
    let term_defs = mk_term_definitions srk dim_of_symbol terms in
    let translate interp dim =
      let num_terms = Array.length terms in
      if dim >= num_terms then
        Interpretation.real interp (Syntax.symbol_of_int (dim - num_terms))
      else if dim >= 0 && dim < num_terms then
        Interpretation.evaluate_term interp terms.(dim)
      else
        begin
          logf "interp_dim: %d not defined" dim;
          assert false
        end
    in
    let interp_dim dim =
      if dim >= num_terms then
        Syntax.mk_const srk (Syntax.symbol_of_int (dim - num_terms))
      else
        terms.(dim)
    in
    let abstract interp phi =
      let implicant = Option.get (Interpretation.select_implicant interp phi) in
      logf ~level:`debug "cubify: abstracting @[%a@]"
        (Format.pp_print_list
           ~pp_sep: (fun fmt () -> Format.fprintf fmt ", ")
           (fun fmt atom -> Syntax.Formula.pp srk fmt atom)
        )
        implicant;
      let vec_of_symbol k = V.of_term QQ.one (dim_of_symbol k) in
      let lincond =
        plt_implicant_of_implicant srk vec_of_symbol implicant in
      let is_ints = implicit_is_ints srk vec_of_symbol implicant in
      let imp_p =
        Polyhedron.of_constraints
          (BatEnum.append
             (BatList.enum term_defs) (BatList.enum lincond.p_cond))
      in
      let imp_l = mk_lattice (List.rev_append lincond.l_cond is_ints) in
      let imp_t = mk_lattice lincond.t_cond in
      let plt =
        { poly_part = imp_p
        ; lattice_part = imp_l
        ; tiling_part = imp_t
        }
      in
      test_point_in_polyhedron ~level:`debug "cubify"
        (translate interp) (BatList.of_enum (P.enum_constraints plt.poly_part));
      test_point_in_lattice ~level:`debug `IsInt "cubify"
        (translate interp) (L.generators plt.lattice_part);
      test_point_in_lattice ~level:`debug `NotInt "cubify"
        (translate interp) (L.generators plt.tiling_part);
      plt
    in
    ( LocalAbstraction.{
        abstract
      ; translate
      }
    , interp_dim
    )

end

module CloseStrictIneq : sig

  (** Strict inequalities make projection more complex, so it helps to remove them first.
   *)

  (** For LRA (no lattice and tiling constraints), we can close strict inequalities trivially
      because projection and taking closure commutes.
      The lattice and tiling components of the plt are ignored and dropped.
   *)
  val round_assuming_no_ints: (Plt.t, int -> QQ.t, P.t, int -> QQ.t) LocalAbstraction.t

  (** For LIA: t > 0 <=> t >= 1.
      The lattice and tiling components of the plt are ignored.
   *)
  val round_assuming_all_ints: (Plt.t, int -> QQ.t, Plt.t, int -> QQ.t) LocalAbstraction.t

  (** Round by shifting t downwards by at most epsilon;
      t > 0 ==> t >= epsilon if t(m) >= epsilon.
   *)
  val round_epsilon: QQ.t -> (Plt.t, int -> QQ.t, Plt.t, int -> QQ.t) LocalAbstraction.t

  (** Use the intersection of the level set of the model with the polyhedron, ignoring
      tiling constraints; this is safe because we are computing the closed convex hull.
   *)
  val polyhedral_level_set: (Plt.t, int -> QQ.t, P.t, int -> QQ.t) LocalAbstraction.t

end = struct

  let close_ineqs ineqs =
    BatEnum.map
      (fun (kind, cnstrnt) ->
        match kind with
        | `Zero -> (`Zero, cnstrnt)
        | `Nonneg -> (`Nonneg, cnstrnt)
        | `Pos -> (`Nonneg, cnstrnt)
      )
      ineqs

  let round_assuming_no_ints =
    LocalAbstraction.{
        abstract = (fun _m plt ->
          close_ineqs (P.enum_constraints (Plt.poly_part plt))
          |> P.of_constraints)
      ; translate = (fun m -> m)
    }

  let rounding_closure ~round_pos =
    let abstract m plt =
      let p = Plt.poly_part plt in
      let p' = BatEnum.map
                 (fun (kind, cnstrnt) ->
                   match kind with
                   | `Zero -> (`Zero, cnstrnt)
                   | `Nonneg -> (`Nonneg, cnstrnt)
                   | `Pos -> (`Nonneg, round_pos m cnstrnt)
                 )
                 (P.enum_constraints p)
               |> P.of_constraints
      in
      Plt.mk_plt ~poly_part:p'
        ~lattice_part:(Plt.lattice_part plt)
        ~tiling_part:(Plt.tiling_part plt)
    in
    LocalAbstraction.{
      abstract
    ; translate = (fun m -> m)
    }

  let round_assuming_all_ints =
    let round_pos _m v =
      if V.equal v V.zero then
        V.of_term (QQ.of_int (-1)) Linear.const_dim
      else
        let d = V.gcd_entries v in
        V.sub v (V.of_term d Linear.const_dim)
    in
    rounding_closure ~round_pos

  let round_epsilon epsilon =
    let round_pos m v =
      let level = Linear.evaluate_affine m v in
      let nudge = QQ.min level epsilon in
      V.sub v (V.of_term nudge Linear.const_dim)
    in
    rounding_closure ~round_pos

  let polyhedral_level_set =
    let abstract m plt =
      let ineqs = close_ineqs (P.enum_constraints (Plt.poly_part plt)) in
      let level_set =
        let equalities = BatEnum.empty () in
        BatList.iter
          (fun v ->
            let const = Linear.evaluate_affine m v in
            BatEnum.push equalities (`Zero, V.add_term (QQ.negate const) Linear.const_dim v)
          )
          (L.generators (Plt.lattice_part plt));
        equalities
      in
      P.of_constraints (BatEnum.append ineqs level_set)
    in
    LocalAbstraction.{
        abstract
      ; translate = (fun m -> m)
    }

end

type virtual_term =
  | PlusInfinity of QQ.t
  | MinusInfinity of QQ.t
  | Term of V.t
  | PlusEpsilon of V.t

let pp_virtual_term fmt vt =
  match vt with
  | PlusInfinity _ -> Format.fprintf fmt "+oo"
  | MinusInfinity _ -> Format.fprintf fmt "-oo"
  | Term t -> pp_vector fmt t
  | PlusEpsilon t -> Format.fprintf fmt "%a + epsilon" pp_vector t

module LwCooper: sig
  val select_vt : ((int -> QQ.t) -> V.t -> V.t) ->
                  int ->
                  (int -> QQ.t) ->
                  plt_constraints ->
                  virtual_term
  val virtual_sub_formula : 'a context ->
                            (symbol -> V.t) ->
                            (int -> 'a arith_term) ->
                            int ->
                            virtual_term ->
                            'a formula ->
                            'a formula

  val virtual_sub : int -> virtual_term -> plt_constraints -> plt_constraints
  (** [local_project] is a simultaneous generalization of
      Cooper-based model-based projection for linear integer arithmetic and
      Loos-Weispfenning-based model-based projection for linear real arithmetic.
      For linear integer-real arithmetic, [local_project] is sound (i.e., a local abstraction)
      but may not have finite image.

      Let PLT(x, Y) be a PLT in dimensions RR^{x \cup Y}.
      [round_up: QQ^{x \cup Y} -> Term(Y) -> Term(Y)] is a function such that
      for all terms [t], [t'] and [m] in PLT(x, Y),
      [round_up m t = t'] only if m(t(y)) <= m(t'(y)) <= m(x).

      If [round_up] has finite image for each [t], [abstract_cooper] is a
      local abstraction that has finite image.
   *)
  val local_project:
    elim: (int -> bool) ->
    round_up: ((int -> QQ.t) -> V.t -> V.t) ->
    (Plt.t, int -> QQ.t, Plt.t, int -> QQ.t) LocalAbstraction.t

  val real_local_project:
    elim: (int -> bool) ->
    (P.t, int -> QQ.t, P.t, int -> QQ.t) LocalAbstraction.t

  val local_project_plt:
    elim: (int -> bool) ->
    (int -> QQ.t) ->
    plt_constraints ->
    plt_constraints
end = struct

  let substitute_for_in v dim w =
    let (coeff, w') = V.pivot dim w in
    V.add (V.scalar_mul coeff v) w'


  let p_false = (`Pos, Linear.const_linterm QQ.zero)
  let l_false = Linear.const_linterm (QQ.of_frac 1 2)
  let p_true = (`Nonneg, Linear.const_linterm QQ.zero)
  let t_true = Linear.const_linterm (QQ.of_frac 1 2)

  let virtual_sub_p vt dim (kind, v) =
    let (coeff, _) = V.pivot dim v in
    let result =
      if QQ.equal coeff QQ.zero then
        (kind, v)
      else
        match (vt, QQ.lt QQ.zero coeff) with
        | (PlusInfinity _, true) ->
           begin match kind with
           | `Zero -> p_false
           | `Nonneg | `Pos -> p_true
           end
        | (MinusInfinity _, false) ->
           begin match kind with
           | `Zero -> p_false
           | `Nonneg | `Pos -> p_true
           end
        | (PlusInfinity _, false) -> p_false
        | (MinusInfinity _, true) -> p_false
        | (Term t, _) ->
           (kind, substitute_for_in t dim v)
        | (PlusEpsilon t, true)->
           begin match kind with
           | `Zero -> p_false
           | `Nonneg | `Pos -> (`Nonneg, substitute_for_in t dim v)
           end
        | (PlusEpsilon t, false)->
           begin match kind with
           | `Zero -> p_false
           | `Nonneg | `Pos -> (`Pos, substitute_for_in t dim v)
           end
    in
    logf ~level:`trace "virtual substitution: substituting %a for %d in @[%a@]"
      pp_virtual_term vt
      dim pp_pconstr (kind, v);
    logf ~level:`trace "virtual substitution: result is @[%a@]"
      pp_pconstr result;
    result

  (* TODO: Verify that there is only one possibility in the range
     [0, lcm of denom)
   *)
  let virtual_sub_l vt dim v =
    let (coeff, _) = V.pivot dim v in
    if QQ.equal coeff QQ.zero then v
    else
      match vt with
      | PlusInfinity delta | MinusInfinity delta ->
         substitute_for_in (Linear.const_linterm delta) dim v
      | Term t -> substitute_for_in t dim v
      | PlusEpsilon _ -> l_false

  let virtual_sub_t vt dim v =
    let (coeff, _) = V.pivot dim v in
    if QQ.equal coeff QQ.zero then v
    else
      match vt with
      | PlusInfinity delta | MinusInfinity delta ->
         substitute_for_in (Linear.const_linterm delta) dim v
      | Term t -> substitute_for_in t dim v
      | PlusEpsilon _ -> t_true

  let glb_for dim p m =
    let has_upper_bound = ref false in
    let argmax (kind1, lower_bound1, b1) (kind2, lower_bound2, b2) =
      if QQ.lt b1 b2 then (kind2, lower_bound2, b2)
      else if QQ.lt b2 b1 then (kind1, lower_bound1, b1)
      else
        begin
          match (kind1, kind2) with
          | (`Nonneg, `Pos)
            | (`Nonneg, `Zero)
            | (`Pos, `Zero) -> (kind2, lower_bound2, b2)
          | (_, _) -> (kind1, lower_bound1, b1)
        end
    in
    let glb = ref None in
    let set_glb lb =
      logf ~level:`debug "glb_for: setting lower bound @[%a@]"
        pp_vector (let (_, lower_bound, _) = lb in lower_bound);
      glb := Some lb
    in
    List.iter
      (fun (kind, v) ->
        logf ~level:`debug "glb_for: @[%a@]"
          pp_pconstr (kind, v);
        let (coeff, w) = V.pivot dim v in
        if QQ.equal QQ.zero coeff then
          ()
        else
          let lower_bound = V.scalar_mul (QQ.negate (QQ.inverse coeff)) w in
          let b = Linear.evaluate_affine m lower_bound in
          if QQ.lt QQ.zero coeff then
            begin
              let () =
                match kind with
                | `Zero -> has_upper_bound := true
                | _ -> ()
              in
              match !glb with
              | None ->
                 set_glb (kind, lower_bound, b)
              | Some (kind0, lower_bound0, b0) ->
                 set_glb (argmax (kind0, lower_bound0, b0) (kind, lower_bound, b))
            end
          else
            begin
              has_upper_bound := true;
              match kind with
              | `Zero ->
                 begin match !glb with
                 | None ->
                    set_glb (kind, lower_bound, b)
                 | Some (kind0, lower_bound0, b0) ->
                    set_glb (argmax (kind0, lower_bound0, b0) (kind, lower_bound, b))
                 end
              | _ -> ()
            end
      )
      p;
    (!glb, !has_upper_bound)

  let select_vt round_up elim_dim m (p, l, t) =
    let gcd_coeffs =
      List.fold_left (fun gcd v -> QQ.gcd (V.coeff elim_dim v) gcd) QQ.zero
        (List.rev_append l t)
    in
    let (continuous, modulus, delta) =
      (* Better than just lcm of denoms, e.g., smaller steps for coeffs 5/2, 5/3 *)
      if QQ.equal QQ.zero gcd_coeffs then (true, QQ.one, QQ.zero)
      else
        let modulus = QQ.inverse gcd_coeffs in
        (false, modulus, QQ.modulo (m elim_dim) modulus)
    in
    let vt =
      match glb_for elim_dim p m with
      | (_, false) -> PlusInfinity delta
      | (None, _) -> MinusInfinity delta
      | (Some (kind, lower, _value), true) ->
         let rounded = round_up m lower in
         let lower_point = Linear.evaluate_affine m lower in
         let rounded_point = Linear.evaluate_affine m rounded in
         let remainder =
           if continuous then QQ.zero
           else QQ.modulo (QQ.sub (m elim_dim) rounded_point) modulus
         in
         let rounded_plus delta = V.add_term delta Linear.const_dim rounded in
         match (kind, QQ.equal QQ.zero remainder) with
         | (`Zero, _) | (`Nonneg, _) | (`Pos, false) -> Term (rounded_plus remainder)
         | (`Pos, true) ->
            assert (QQ.leq lower_point rounded_point);
            if continuous then PlusEpsilon rounded
            else if QQ.lt lower_point rounded_point then Term rounded
            else Term (rounded_plus modulus) (* move up one level *)
    in
    logf ~level:`debug "LwCooper.select_vt: selected %a" pp_virtual_term vt;
    vt

  let virtual_sub dim vt (p, l, t) =
    (List.map (virtual_sub_p vt dim) p,
     List.map (virtual_sub_l vt dim) l,
     List.map (virtual_sub_t vt dim) t)

  let virtual_sub_formula srk vec_of_sym term_of_dim dim vt formula =
    let subst_atom = function
      | (`Pos, t) -> formula_p srk term_of_dim (virtual_sub_p vt dim (`Pos, t))
      | (`Zero, t) -> formula_p srk term_of_dim (virtual_sub_p vt dim (`Zero, t))
      | (`Nonneg, t) -> formula_p srk term_of_dim (virtual_sub_p vt dim (`Nonneg, t))
      | (`IsInt, t) -> formula_l srk term_of_dim (virtual_sub_l vt dim t)
      | (`NotInt, t) -> formula_t srk term_of_dim (virtual_sub_t vt dim t)
    in
    let subst = function
      | `Atom at -> subst_atom at
      | `Tru -> mk_true srk
      | `Fls -> mk_false srk
      | `And xs -> mk_and srk xs
      | `Or xs -> mk_or srk xs
      | `Quantify (_, _, _, _) ->
         invalid_arg "Cannot apply virtual substitution to a quantified formula"
    in
    Linear.eval_lira srk ~vec_of_sym subst formula

  let project_one round_up elim_dim m (p, l, t) =
    logf ~level:`debug "lwcooper_project_one: eliminating %d" elim_dim;
    let vt = select_vt round_up elim_dim m (p, l, t) in
    let (polyhedron, lattice, tiling) = virtual_sub elim_dim vt (p, l, t) in
    test_point_in_polyhedron "LwCooper.project_one" m polyhedron;
    test_point_in_lattice `IsInt "LwCooper.project_one" m lattice;
    test_point_in_lattice `NotInt "LwCooper.project_one" m tiling;
    (polyhedron, lattice, tiling)

  let local_project_plt ~elim m (p, l, t) =
    let elim_dimensions =
      collect_dimensions (fun (_, v) -> v) elim p
      |> IntSet.union (collect_dimensions (fun v -> v) elim l)
      |> IntSet.union (collect_dimensions (fun v -> v) elim t)
    in
    IntSet.fold (fun elim_dim (p, l, t) ->
        project_one (fun _ v -> v) elim_dim m (p, l, t))
      elim_dimensions
      (p, l, t)

  let local_project_ ~elim ~round_up m plt =
    let open Plt in
    let p = P.enum_constraints (Plt.poly_part plt) |> BatList.of_enum in
    let l = L.generators (Plt.lattice_part plt) in
    let t = L.generators (Plt.tiling_part plt) in
    let elim_dimensions =
      Plt.constrained_dimensions plt
      |> IntSet.filter elim
    in
    logf ~level:`debug "LwCooper.local_project: eliminating dimensions @[%a@] from@\n"
      IntSet.pp elim_dimensions;
    log_plt_constraints ~level:`debug "plt: " (p, l, t);
    let (projected_p, projected_l, projected_t) =
      IntSet.fold
        (fun elim_dim (p, l, t) ->
          project_one round_up elim_dim m (p, l, t)
        )
        elim_dimensions
        (p, l, t)
    in
    logf ~level:`debug "LwCooper.local_project: abstracted";
    mk_plt ~poly_part:(Polyhedron.of_constraints (BatList.enum projected_p))
      ~lattice_part:(L.of_generators projected_l)
      ~tiling_part:(L.of_generators projected_t)

  let local_project ~elim ~round_up =
    let restricted m dim =
      if elim dim then
        failwith
          (Format.asprintf
             "abstract_lw: Dimension %d has been eliminated" dim)
      else m dim
    in
    LocalAbstraction.
    {
      abstract = local_project_ ~elim ~round_up
    ; translate = restricted
    }

  let real_local_project ~elim =
    let local_project = local_project ~elim ~round_up:(fun _m v -> v) in
    let abstract m p =
      let plt = Plt.mk_plt
                  ~poly_part:p ~lattice_part:L.bottom ~tiling_part:L.bottom
      in
      local_project.abstract m plt |> Plt.poly_part
    in
    LocalAbstraction.{
      abstract
    ; translate = local_project.translate
    }

end

module LocalHull: sig

  (** Compute a (closed) polyhedron that is a subset of the closed convex hull of
      the input [plt].
      The polyhedral part of [plt] MUST be closed.
   *)
  val local_hull: man:DD.closed Apron.Manager.t ->
                  ambient_dim:int ->
                  (Plt.t, int -> Q.t, DD.closed DD.t, int -> Q.t) LocalAbstraction.t

end = struct

  (* This function requires that the polyhedron in plt to be closed. *)
  let local_hull ~man ~(ambient_dim:int) :
        (Plt.t, int -> QQ.t, DD.closed DD.t, int -> QQ.t) LocalAbstraction.t =
    let abstract m plt =
      let p = Plt.poly_part plt in
      let m_vec =
        let open BatPervasives in
        BatEnum.fold
          (fun v i -> V.add_term (m i) i v)
          V.zero
          (0 --^ ambient_dim)
      in
      let fns =
        let covectors =
          (L.generators (Plt.lattice_part plt))
          @ (L.generators (Plt.tiling_part plt))
        in
        (* Taking the dot-product with the lattice / tiling constraints
           effectively homogenizes them, since the coefficient
           Linear.const_dim is zero for every point in the primal space. *)
        List.map (fun vec -> V.dot vec) covectors
      in
      let dd = P.dd_of ~man ambient_dim p in
      let generators =
        BatEnum.map (fun (k, v) ->
            match k with
            | `Vertex ->
               let int_v =
                 P.close_lattice_point fns p ~rational:v ~integer:m_vec ambient_dim
               in
               (`Vertex, int_v)
            | `Ray -> (`Ray, v)
            | `Line -> (`Line, v)
          )
          (DD.enum_generators dd)
      in
      BatEnum.push generators (`Vertex, m_vec); (* to ensure the abstraction property *)
      (DD.of_generators ~man ambient_dim generators)
    in
    LocalAbstraction.{
        abstract
      ; translate = (fun m -> m)
    }

end

module PltConvexHull : sig

  val local_project_local_hull:
    man:DD.closed Apron.Manager.t ->
    max_dim_in_target:int ->
    epsilon:Q.t ->
    (Plt.t, int -> Q.t, DD.closed DD.t, int -> Q.t) LocalAbstraction.t

  (** This is a compact local abstraction. *)
  val local_project_polyreccone :
    man:DD.closed Apron.Manager.t ->
    max_dim_in_target:int ->
    (Plt.t, int -> Q.t, DD.closed DD.t, int -> Q.t) LocalAbstraction.t

  val by_polyreccone_and_lplh:
    man:DD.closed Apron.Manager.t ->
    max_dim_in_target:int ->
    epsilon:QQ.t ->
    (Plt.t, int -> Q.t, DD.closed DD.t, int -> Q.t) LocalAbstraction.t

end = struct

  let local_project_local_hull ~man ~max_dim_in_target ~epsilon =
    let elim dim = dim > max_dim_in_target in
    CloseStrictIneq.round_epsilon epsilon
    |> LocalAbstraction.compose (LwCooper.local_project ~elim ~round_up:(fun _m v -> v))
    |> LocalAbstraction.compose (LocalHull.local_hull ~man ~ambient_dim:(max_dim_in_target + 1))

  let local_project_polyreccone ~man ~max_dim_in_target =
    let elim dim = dim > max_dim_in_target in
    let abstract m plt =
      let projected_polyhedron_generators =
        CloseStrictIneq.polyhedral_level_set.abstract m plt
        |> (LwCooper.real_local_project ~elim).abstract m
        |> P.dd_of ~man (max_dim_in_target + 1)
        |> DD.enum_generators
      in
      let reccone_generators =
        CloseStrictIneq.round_assuming_no_ints.abstract m plt
        |> (LwCooper.real_local_project ~elim).abstract m
        |> P.dd_of ~man (max_dim_in_target + 1)
        |> DD.enum_generators
        |> BatEnum.filter (fun (kind, _) -> kind = `Ray || kind = `Line)
      in
      BatEnum.append projected_polyhedron_generators reccone_generators
      |> DD.of_generators ~man (max_dim_in_target + 1)
    in
    LocalAbstraction.{
      abstract
    ; translate =
        (fun m dim ->
          if dim > max_dim_in_target then
            failwith
              (Format.asprintf
                 "local_project_polyreccone: Dimension %d has been eliminated" dim)
         else m dim)
    }

  let by_polyreccone_and_lplh ~man ~max_dim_in_target ~epsilon =
    LocalAbstraction.join DD.join
      (local_project_polyreccone ~man ~max_dim_in_target)
      (local_project_local_hull ~man ~max_dim_in_target ~epsilon)

end

module ConvexHull : sig

  (** Local abstraction algorithms for computing the closed convex hull of the image of
      the set of models of an LRA, LIA, or LIRA formula under a linear map
      defined by a set of terms.

      More precisely,
      if [alpha = convex_hull srk terms symbols],
      [alpha m F] is the convex hull of { T(m): m |= F }, where
      [T(m) = (terms[0](m), ..., terms[length(terms)-1](m))];
      [t(m)] is the evaluation of term [t] on [m].

      Formulas should only have linear real arithmetic terms,
      i.e., no floor, mod, non-trivial multiplication and division, etc.
   *)

  (** All symbols should be of real type,
      and all atoms are equalities or inequalities, i.e., no [is_int]'s.
      Otherwise, it is an over-approximation of the result.
   *)
  val by_lp_assuming_real:
    ?man: DD.closed Apron.Manager.t ->
    'a context -> 'a arith_term array -> Symbol.Set.t ->
    ('a formula, 'a Interpretation.interpretation, DD.closed DD.t, int -> QQ.t) LocalAbstraction.t

  val by_full_project_assuming_real:
    ?man:Polka.loose Polka.t Apron.Manager.t ->
    'a context ->
    'a arith_term array ->
    Symbol.Set.t ->
    ('a formula, 'a Interpretation.interpretation, DD.closed DD.t, int -> Q.t) LocalAbstraction.t

  (** All symbols must be of integer type, and all terms must have integer coefficients.
      Local-project-local-hull is (sound and) compact when these conditions hold.

      For the latter condition, rounding assuming integer-valued variables is in general
      unsound.
      E.g.: t = 1/2 x + y, is_int(x), is_int(y), 1/2 x + y > 0,
      i.e., 1/2 x + y >= 1/2.
      Eliminating y gives t > 0 /\ is_int(t - 1/2 x).
      Then rounding gives t >= 1 /\ is_int(t - 1/2 x), i.e.,
      1/2 x + y >= 1.
      This is not equivalent to the original formula, and is not a local abstraction:
      consider (x, y) = (1, 0).
   *)
  val by_lplh_assuming_integer:
    ?man: DD.closed Apron.Manager.t ->
    'a context -> 'a arith_term array -> Symbol.Set.t ->
    ('a formula, 'a Interpretation.interpretation, DD.closed DD.t, int -> QQ.t) LocalAbstraction.t

  val by_hull_then_project_assuming_integer:
    [`GomoryChvatal | `Normaliz ] ->
    ?man:DD.closed Apron.Manager.t ->
    'a context ->
    'a arith_term array ->
    Symbol.Set.t ->
    ('a formula, 'a Interpretation.interpretation, DD.closed DD.t, int -> Q.t) LocalAbstraction.t

  val by_polyreccone:
    ?man: DD.closed Apron.Manager.t ->
    'a context -> 'a arith_term array -> Symbol.Set.t ->
    ('a formula, 'a Interpretation.interpretation, DD.closed DD.t, int -> QQ.t) LocalAbstraction.t

  val by_lplh:
    ?man: DD.closed Apron.Manager.t -> epsilon: QQ.t ->
    'a context -> 'a arith_term array -> Symbol.Set.t ->
    ('a formula, 'a Interpretation.interpretation, DD.closed DD.t, int -> QQ.t) LocalAbstraction.t

  val by_polyreccone_and_lplh:
    ?man: DD.closed Apron.Manager.t -> epsilon: QQ.t ->
    'a context -> 'a arith_term array -> Symbol.Set.t ->
    ('a formula, 'a Interpretation.interpretation, DD.closed DD.t, int -> QQ.t) LocalAbstraction.t

end = struct

  let ddify ~man ambient_dim =
    let abstract _m p =
      P.dd_of ~man ambient_dim p
    in
    LocalAbstraction.{
      abstract
    ; translate = (fun m -> m)
    }

  let by_lp_assuming_real ?(man=Polka.manager_alloc_loose()) srk terms symbols =
    let (cubify, _) = Plt.cubify srk terms symbols in
    let elim dim = dim >= Array.length terms in
    cubify
    |> LocalAbstraction.compose CloseStrictIneq.round_assuming_no_ints
    |> LocalAbstraction.compose (LwCooper.real_local_project ~elim)
    |> LocalAbstraction.compose (ddify ~man (Array.length terms))

  let restrict target_dim m dim =
    if dim < 0 || dim >= target_dim then
      invalid_arg (Format.asprintf "dimension %d cannot be interpreted" dim)
    else m dim

  let by_full_project_assuming_real
        ?(man=Polka.manager_alloc_loose()) srk terms symbols =
    let project =
      let abstract _m p =
        let max_dim_in_p = P.max_constrained_dim p in
        let dimensions_to_eliminate =
          BatEnum.(Array.length terms -- max_dim_in_p) |> BatList.of_enum
        in
        P.project_dd dimensions_to_eliminate p
        |> P.dd_of ~man (Array.length terms)
      in
      LocalAbstraction.{ abstract; translate = restrict (Array.length terms) }
    in
    let (cubify, _) = Plt.cubify srk terms symbols in
    cubify
    |> LocalAbstraction.compose CloseStrictIneq.round_assuming_no_ints
    |> LocalAbstraction.compose project

  let by_lplh_assuming_integer ?(man=Polka.manager_alloc_loose()) srk terms symbols =
    let (cubify, _) = Plt.cubify srk terms symbols in
    let target_dim = Array.length terms in
    let elim dim = dim >= Array.length terms in
    cubify
    |> LocalAbstraction.compose CloseStrictIneq.round_assuming_all_ints
    |> LocalAbstraction.compose (LwCooper.local_project ~elim ~round_up:(fun _m v -> v))
    |> LocalAbstraction.compose (LocalHull.local_hull ~man ~ambient_dim:target_dim)

  let by_hull_then_project_assuming_integer
        hull_alg
        ?(man=Polka.manager_alloc_loose()) srk terms symbols =
    let target_dim = Array.length terms in
    let project =
      let abstract _m plt =
        let p = Plt.poly_part plt in
        let max_dim_in_p = P.max_constrained_dim p in
        let dimensions_to_eliminate =
          BatEnum.(target_dim -- max_dim_in_p) |> BatList.of_enum in
        let project_and_rebuild dd =
          DD.project dimensions_to_eliminate dd
          |> DD.enum_constraints
          |> DD.of_constraints_closed ~man target_dim
        in
        match hull_alg with
        | `GomoryChvatal ->
           P.dd_of ~man (max_dim_in_p + 1) p
           |> DD.integer_hull
           |> project_and_rebuild
        | `Normaliz ->
           P.integer_hull `Normaliz p
           |> P.dd_of ~man (max_dim_in_p + 1)
           |> project_and_rebuild
      in
      LocalAbstraction.{ abstract; translate = restrict target_dim }
    in
    let (cubify, _) = Plt.cubify srk terms symbols in
    cubify
    |> LocalAbstraction.compose CloseStrictIneq.round_assuming_all_ints
    |> LocalAbstraction.compose project

  let by_polyreccone_and_lplh ?(man=Polka.manager_alloc_loose()) ~epsilon srk terms symbols =
    let (cubify, _) = Plt.cubify srk terms symbols in
    let max_dim_in_target = Array.length terms - 1 in
    let compose = LocalAbstraction.compose in
    cubify
    |> compose (PltConvexHull.by_polyreccone_and_lplh ~man ~epsilon ~max_dim_in_target)

  let by_lplh ?(man=Polka.manager_alloc_loose()) ~epsilon srk terms symbols =
    let (cubify, _) = Plt.cubify srk terms symbols in
    let max_dim_in_target = Array.length terms - 1 in
    let compose = LocalAbstraction.compose in
    cubify
    |> compose (PltConvexHull.local_project_local_hull ~man ~epsilon ~max_dim_in_target)

  let by_polyreccone ?(man=Polka.manager_alloc_loose()) srk terms symbols =
    let (cubify, _) = Plt.cubify srk terms symbols in
    let max_dim_in_target = Array.length terms - 1 in
    let compose = LocalAbstraction.compose in
    cubify
    |> compose (PltConvexHull.local_project_polyreccone ~man ~max_dim_in_target)

end

module LocalGlobal: sig

  val lift:
    man:DD.closed Apron.Manager.t ->
    ('a formula, 'a Interpretation.interpretation, DD.closed DD.t, int -> QQ.t) LocalAbstraction.t ->
    'a Abstract.Solver.t -> ?bottom: DD.closed DD.t -> ('a arith_term) Array.t -> DD.closed DD.t

end = struct

  let print_model srk terms interp =
    let result =
      Array.init (Array.length terms)
        (fun i ->
          (terms.(i), Interpretation.evaluate_term interp terms.(i)))
    in
    logf ~level:`debug "model: @[%a@]@;"
      (Format.pp_print_list
         ~pp_sep:(fun fmt () -> Format.fprintf fmt "; ")
         (fun fmt (t, value) ->
           Format.fprintf fmt "(%a, %a)"
             (Syntax.ArithTerm.pp srk) t
             QQ.pp value))
      (Array.to_list result)

  let lift ~man local_abs solver ?bottom terms =
    let target_dim = Array.length terms in
    let bottom =
      match bottom with
      | None -> P.dd_of ~man target_dim P.bottom
      | Some bot -> bot
    in
    let top = P.dd_of ~man target_dim P.top in
    let srk = Abstract.Solver.get_context solver in
    let phi = Abstract.Solver.get_formula solver in
    let counter = ref 0 in
    let models = ref [] in
    let show m =
      let symbols =
        Syntax.Symbol.Set.elements (Syntax.symbols phi)
        |> List.map (Syntax.mk_const srk) |> Array.of_list
      in
      print_model srk symbols m
    in
    let of_model m =
      match m with
      | `LIRR _ -> invalid_arg "LIRR not supported"
      | `LIRA m ->
         let () = show m in
         models := m :: !models;
         counter := !counter + 1;

         logf ~level:`debug "Abstraction loop iteration: %d" !counter;
         let result = local_abs.LocalAbstraction.abstract m phi in
         logf ~level:`debug "Abstraction loop iteration %d done" !counter;
         result
    in
    let domain =
      Abstract.
      { join = DD.join
      ; of_model
      ; formula_of = formula_of_dd srk (fun i -> terms.(i))
      ; top
      ; bottom
      }
    in
    Abstract.Solver.abstract solver domain

end

type lira_abstraction =
  | PolyReccone
  | LiraLPLH of QQ.t option
  | PolyReccone_LPLH of QQ.t option

type lia_abstraction =
  | HullThenProject of [`GomoryChvatal | `Normaliz]
  | LiaLPLH

type lra_abstraction =
  | FullProject
  | LwMbp

type abstraction_algorithm =
  | LiraCCH of lira_abstraction
  | LiaCCH of lia_abstraction
  | LraCCH of lra_abstraction

let default_epsilon = ref (QQ.of_frac 1 10)

let local_abstraction ~man srk terms symbols how =
  match how with
  | LiraCCH PolyReccone ->
     ConvexHull.by_polyreccone ~man srk terms symbols
  | LiraCCH (LiraLPLH eps) ->
     let epsilon = match eps with | None -> !default_epsilon | Some epsilon -> epsilon
     in
     ConvexHull.by_lplh ~man ~epsilon srk terms symbols
  | LiraCCH (PolyReccone_LPLH eps) ->
     let epsilon = match eps with | None -> !default_epsilon | Some epsilon -> epsilon
     in
     ConvexHull.by_polyreccone_and_lplh ~man ~epsilon srk terms symbols
  | LiaCCH (HullThenProject `GomoryChvatal) ->
     ConvexHull.by_hull_then_project_assuming_integer `GomoryChvatal ~man srk terms symbols
  | LiaCCH (HullThenProject `Normaliz) ->
     ConvexHull.by_hull_then_project_assuming_integer `Normaliz ~man srk terms symbols
  | LiaCCH LiaLPLH ->
     ConvexHull.by_lplh_assuming_integer ~man srk terms symbols
  | LraCCH FullProject ->
     ConvexHull.by_full_project_assuming_real ~man srk terms symbols
  | LraCCH LwMbp ->
     ConvexHull.by_lp_assuming_real ~man srk terms symbols

let convex_hull_from_lira_model
      how ?(man=Polka.manager_alloc_loose ()) solver terms model =
  let srk = Abstract.Solver.get_context solver in
  let phi = Abstract.Solver.get_formula solver in
  let symbols = Syntax.symbols phi in
  let m = match model with
    | `LIRA m -> m
    | `LIRR _ -> invalid_arg "Unsupported"
  in
  let abstraction = local_abstraction ~man srk terms symbols how in
  abstraction.abstract m phi

let abstract
      how ?(man=Polka.manager_alloc_loose ()) ?(bottom=None)
      solver terms =
  let srk = Abstract.Solver.get_context solver in
  let phi = Abstract.Solver.get_formula solver in
  let symbols = Syntax.symbols phi in
  let bottom =
    match bottom with
    | None -> P.dd_of (Array.length terms) P.bottom
    | Some bot -> bot
  in
  LocalGlobal.lift ~man (local_abstraction ~man srk terms symbols how) solver ~bottom terms

let convex_hull how ?(man=Polka.manager_alloc_loose ()) srk phi terms =
  let solver = Abstract.Solver.make srk ~theory:`LIRA phi in
  abstract how ~man solver terms

let _formula_of_plt = Plt.formula_of_plt

let realify_formula_and_terms srk phi terms =
  let (phi', map) = Syntax.retype srk `IntToReal Symbol.Map.empty phi in
  let accumulated_map =
    Array.fold_left
      (fun acc_map term ->
        let (_, map') = Syntax.retype srk `IntToReal acc_map term in map'
      )
      map
      terms
  in
  let lookup s = match Syntax.Symbol.Map.find_opt s accumulated_map with
    | Some s' -> Syntax.mk_const srk s'
    | None -> Syntax.mk_const srk s
  in
  let terms' = Array.map (fun term -> Syntax.substitute_const srk lookup term) terms
  in
  (phi', terms', accumulated_map)

let select_vt = LwCooper.select_vt (fun _m v -> v)
let virtual_subst
      srk
      ?(vec_of_sym=default_vec_of_sym)
      ?(term_of_dim=default_term_of_dim)
  =
  LwCooper.virtual_sub_formula srk vec_of_sym (term_of_dim srk)

let virtual_subst_plt = LwCooper.virtual_sub

let select_plt srk ?(vec_of_sym=default_vec_of_sym) phi interp =
  match Interpretation.select_implicant interp phi with
  | None -> None
  | Some cube -> Some (Plt.plt_constraints_of_cube srk vec_of_sym cube)

let local_project_plt = LwCooper.local_project_plt

let poly_part (p, _, _) = p
let lattice_part (_, l, _) = l
let tiling_part (_, _, t) = t

let make_plt_constraints ?(lattice_part=[]) ?(tiling_part=[]) poly_part =
  (poly_part, lattice_part, tiling_part)

let formula_of_plt = Plt.formula_of_plt_constraints
