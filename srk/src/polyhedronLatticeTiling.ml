open Syntax
module P = Polyhedron
module L = IntLattice

module V = Linear.QQVector

include Log.Make (struct let name = "srk.polyhedronLatticeTiling" end)

let eager_hermite = ref false

type ('concept1, 'model1, 'concept2, 'model2) local_abstraction =
  ('concept1 * 'model1) -> ('concept2 * 'model2)

let join join_operator local_abs1 local_abs2 (concept, model) =
  let hull1 = local_abs1 (concept, model) in
  let hull2 = local_abs2 (concept, model) in
  ( join_operator (fst hull1) (fst hull2)
  , snd hull1
  )

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

let formula_l srk term_of_dim v =
  let t = term_of_vec srk term_of_dim v in
  mk_is_int srk t

let formula_t srk term_of_dim v =
  let t = term_of_vec srk term_of_dim v in
  mk_not srk (mk_is_int srk t)

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
    'a context -> 'a arith_term array ->
    ('a formula, 'a Interpretation.interpretation, t, int -> QQ.t)
      local_abstraction
    * (int -> 'a arith_term)

  val poly_part: t -> P.t
  val lattice_part: t -> L.unreduced L.t
  val tiling_part: t -> L.unreduced L.t

  val mk_plt:
    poly_part:P.t ->
    lattice_part: L.unreduced L.t -> tiling_part: L.unreduced L.t -> t

  val plt_constraints_of_cube : 'a context
    -> (symbol -> V.t) -> 'a formula list -> plt_constraints

  val formula_of_plt_constraints: 'a Syntax.context
    -> ?term_of_dim:('a context -> int -> 'a arith_term)
    -> plt_constraints -> 'a formula

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
    let phis_p = List.map (P.formula_of_constraint srk term_of_dim) p in
    let phis_l = List.map (formula_l srk term_of_dim) l in
    let phis_t = List.map (formula_l srk term_of_dim) t in
    mk_and srk (phis_p @ phis_l @ phis_t)

  let formula_of_plt srk term_of_dim plt =
    let phis_p =
      BatEnum.map
        (P.formula_of_constraint srk term_of_dim)
        (P.enum_constraints plt.poly_part)
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

  let cubify srk terms =
    let num_terms = Array.length terms in
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
    let abstract phi interp =
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
      plt
    in
    ( (fun (phi, m) -> (abstract phi m, translate m))
    , interp_dim)
end

module CloseStrictIneq : sig

  (** Strict inequalities make projection more complex, so it helps to remove
      them first.
  *)

  (** For LRA (no lattice and tiling constraints), we can close strict
      inequalities trivially because projection and taking closure commutes.
      The lattice and tiling components of the plt are ignored and dropped.
   *)
  val round_assuming_no_ints: (Plt.t, int -> QQ.t, P.t, int -> QQ.t)
    local_abstraction

  (** For LIA: t > 0 <=> t >= 1.
      The lattice and tiling components of the plt are ignored.
   *)
  val round_assuming_all_ints: (Plt.t, int -> QQ.t, Plt.t, int -> QQ.t)
    local_abstraction

  (** Round by shifting t downwards by at most epsilon;
      t > 0 ==> t >= epsilon if t(m) >= epsilon.
   *)
  val round_epsilon: QQ.t -> (Plt.t, int -> QQ.t, Plt.t, int -> QQ.t)
    local_abstraction

  (** Use the intersection of the level set of the model with the polyhedron,
      ignoring tiling constraints; this is safe because we are computing the
      closed convex hull.
   *)
  val polyhedral_level_set: (Plt.t, int -> QQ.t, P.t, int -> QQ.t)
    local_abstraction

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
    fun (plt, m) ->
      ( close_ineqs (P.enum_constraints (Plt.poly_part plt))
        |> P.of_constraints
      , m
      )

  let rounding_closure ~round_pos =
    let abstract plt m =
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
    (fun (plt, m) -> (abstract plt m, m))

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
    let abstract plt m =
      let ineqs = close_ineqs (P.enum_constraints (Plt.poly_part plt)) in
      let level_set =
        let equalities = BatEnum.empty () in
        BatList.iter
          (fun v ->
            let const = Linear.evaluate_affine m v in
            BatEnum.push equalities (`Zero, V.add_term (QQ.negate const)
              Linear.const_dim v)
          )
          (L.generators (Plt.lattice_part plt));
        equalities
      in
      P.of_constraints (BatEnum.append ineqs level_set)
    in
    (fun (plt, m) -> (abstract plt m, m))

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
  val select_vt : int ->
                  (int -> QQ.t) ->
                  plt_constraints ->
                  virtual_term
  val virtual_sub_formula : 'a context ->
                            (symbol -> V.t) ->
                            (int -> 'a arith_term) ->
                            (int * virtual_term) list ->
                            'a formula ->
                            'a formula

  val virtual_sub : (int * virtual_term) list -> plt_constraints -> plt_constraints
  (** [local_project] is a simultaneous generalization of
      Cooper-based model-based projection for linear integer arithmetic and
      Loos-Weispfenning-based model-based projection for linear real arithmetic.
      For linear integer-real arithmetic, [local_project] is sound
      (i.e., a local abstraction) but may not have finite image.
   *)
  val local_project:
    elim: (int -> bool) ->
    (Plt.t, int -> QQ.t, Plt.t, int -> QQ.t) local_abstraction

  val real_local_project:
    elim: (int -> bool) ->
    (P.t, int -> QQ.t, P.t, int -> QQ.t) local_abstraction

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
      logf ~level:`debug "LwCooper.glb_for: setting lower bound @[%a@]"
        pp_vector (let (_, lower_bound, _) = lb in lower_bound);
      glb := Some lb
    in
    List.iter
      (fun (kind, v) ->
        logf ~level:`debug "LwCooper.glb_for: @[%a@]"
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

  let select_vt elim_dim m (p, l, t) =
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
         let lower_point = Linear.evaluate_affine m lower in
         let remainder =
           if continuous then QQ.zero
           else QQ.modulo (QQ.sub (m elim_dim) lower_point) modulus
         in
         let lower_plus delta = V.add_term delta Linear.const_dim lower in
         match (kind, QQ.equal QQ.zero remainder) with
         | (`Zero, _) | (`Nonneg, _) | (`Pos, false) -> Term (lower_plus remainder)
         | (`Pos, true) ->
            if continuous then PlusEpsilon lower
            else Term (lower_plus modulus) (* move up one level *)
    in
    logf ~level:`debug "LwCooper.select_vt: selected %a" pp_virtual_term vt;
    vt

  let virtual_sub sigma (p, l, t) =
    let subst_all f x =
      List.fold_left (fun x (dim, vt) -> f vt dim x) x sigma
    in
    (List.map (subst_all virtual_sub_p) p,
     List.map (subst_all virtual_sub_l) l,
     List.map (subst_all virtual_sub_t) t)

  let virtual_sub_formula srk vec_of_sym term_of_dim sigma formula =
    let subst_all f x =
      List.fold_left (fun x (dim, vt) -> f vt dim x) x sigma
    in
    let subst_atom = function
      | (`Pos, t) ->
          P.formula_of_constraint srk term_of_dim
            (subst_all virtual_sub_p (`Pos, t))
      | (`Zero, t) ->
          P.formula_of_constraint srk term_of_dim
            (subst_all virtual_sub_p (`Zero, t))
      | (`Nonneg, t) ->
          P.formula_of_constraint srk term_of_dim
            (subst_all virtual_sub_p (`Nonneg, t))
      | (`IsInt, t) -> formula_l srk term_of_dim (subst_all virtual_sub_l t)
      | (`NotInt, t) -> formula_t srk term_of_dim (subst_all virtual_sub_t t)
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
    let formula' = Linear.eval_lira srk ~vec_of_sym subst formula in

    (* Make implicit integrality contraint for eliminated dimension explicit *)
    let rec explicit_ints sigma constraints =
      match sigma with
      | [] -> constraints
      | (dim, _)::sigma' ->
         if expr_typ srk (term_of_dim dim) = `TyInt then
           let dim_int =
             List.fold_left (fun x (dim, vt) -> virtual_sub_l vt dim x)
               (V.of_term QQ.one dim)
               sigma
             |> formula_l srk term_of_dim
           in
           explicit_ints sigma' (dim_int::constraints)
         else
           explicit_ints sigma' constraints
    in
    explicit_ints sigma [formula']
    |> mk_and srk


  let project_one elim_dim m (p, l, t) =
    logf ~level:`debug "lwcooper_project_one: eliminating %d" elim_dim;
    let vt = select_vt elim_dim m (p, l, t) in
    let (polyhedron, lattice, tiling) = virtual_sub [(elim_dim, vt)] (p, l, t)
    in
    (polyhedron, lattice, tiling)

  let local_project_plt ~elim m (p, l, t) =
    let elim_dimensions =
      collect_dimensions (fun (_, v) -> v) elim p
      |> IntSet.union (collect_dimensions (fun v -> v) elim l)
      |> IntSet.union (collect_dimensions (fun v -> v) elim t)
    in
    IntSet.fold (fun elim_dim (p, l, t) -> project_one elim_dim m (p, l, t))
      elim_dimensions
      (p, l, t)

  let local_project_ ~elim plt m =
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
          project_one elim_dim m (p, l, t)
        )
        elim_dimensions
        (p, l, t)
    in
    logf ~level:`debug "LwCooper.local_project: abstracted";
    mk_plt ~poly_part:(Polyhedron.of_constraints (BatList.enum projected_p))
      ~lattice_part:(L.of_generators projected_l)
      ~tiling_part:(L.of_generators projected_t)

  let local_project ~elim =
    let restricted m dim =
      if elim dim then
        failwith
          (Format.asprintf
             "LwCooper.local_project: Dimension %d has been eliminated" dim)
      else m dim
    in
    (fun (plt, m) -> local_project_ ~elim plt m, restricted m)

  let real_local_project ~elim =
    let local_project = local_project ~elim in
    let lift p = Plt.mk_plt
      ~poly_part:p ~lattice_part:L.bottom ~tiling_part:L.bottom
    in
    (fun (p, m) ->
      let projected = local_project (lift p, m) in
      (fst projected |> Plt.poly_part, snd projected))

end

module LocalHull: sig

  (** Compute a (closed) polyhedron that is a subset of the closed convex hull
      of the input [plt]. The polyhedral part of [plt] MUST be closed.
   *)
  val local_hull: man:DD.closed Apron.Manager.t ->
                  ambient_dim:int ->
                  (Plt.t, int -> Q.t, DD.closed DD.t, int -> Q.t) local_abstraction

end = struct

  (* This function requires that the polyhedron in plt to be closed. *)
  let local_hull ~man ~(ambient_dim:int) :
        (Plt.t, int -> QQ.t, DD.closed DD.t, int -> QQ.t) local_abstraction =
    let abstract plt m =
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
    fun (plt, m) -> (abstract plt m, m)

end

module PltConvexHull : sig

  val by_polyreccone_and_lplh:
    man:DD.closed Apron.Manager.t ->
    max_dim_in_target:int ->
    epsilon:QQ.t ->
    (Plt.t, int -> Q.t, DD.closed DD.t, int -> Q.t) local_abstraction

end = struct

  let local_project_local_hull ~man ~max_dim_in_target ~epsilon (plt, m) =
    let elim dim = dim > max_dim_in_target in
    CloseStrictIneq.round_epsilon epsilon (plt, m)
    |> LwCooper.local_project ~elim
    |> LocalHull.local_hull ~man ~ambient_dim:(max_dim_in_target + 1)

  let local_project_polyreccone ~man ~max_dim_in_target =
    let elim dim = dim > max_dim_in_target in
    let abstract plt m =
      let projected_polyhedron_generators =
        CloseStrictIneq.polyhedral_level_set (plt, m)
        |> LwCooper.real_local_project ~elim
        |> fst
        |> P.dd_of ~man (max_dim_in_target + 1)
        |> DD.enum_generators
      in
      let reccone_generators =
        CloseStrictIneq.round_assuming_no_ints (plt, m)
        |> LwCooper.real_local_project ~elim
        |> fst
        |> P.dd_of ~man (max_dim_in_target + 1)
        |> DD.enum_generators
        |> BatEnum.filter (fun (kind, _) -> kind = `Ray || kind = `Line)
      in
      BatEnum.append projected_polyhedron_generators reccone_generators
      |> DD.of_generators ~man (max_dim_in_target + 1)
    in
    fun (plt, m) ->
      ( abstract plt m
      , fun dim ->
          if dim > max_dim_in_target then
            failwith
              (Format.asprintf
                "local_project_polyreccone: Dimension %d has been eliminated"
                dim
              )
        else m dim
      )

  let by_polyreccone_and_lplh ~man ~max_dim_in_target ~epsilon =
    join DD.join
      (local_project_polyreccone ~man ~max_dim_in_target)
      (local_project_local_hull ~man ~max_dim_in_target ~epsilon)

end

module ConvexHull : sig

  type 'a lira_to_polyhedron_abs =
    ('a formula, 'a Interpretation.interpretation, DD.closed DD.t, (int -> QQ.t))
    local_abstraction

  (** Local abstraction algorithms for computing the closed convex hull of the
      image of the set of models of an LRA, LIA, or LIRA formula under a
      linear map defined by a set of terms.

      More precisely,
      if [alpha = convex_hull srk terms symbols],
      [alpha m F] is the convex hull of { T(m): m |= F }, where
      [T(m) = (terms[0](m), ..., terms[length(terms)-1](m))];
      [t(m)] is the evaluation of term [t] on [m].

      Formulas should only have linear real arithmetic terms,
      i.e., no floor, mod, non-trivial multiplication and division, etc.
   *)

  val cch_lira:
    man:DD.closed Apron.Manager.t -> ?epsilon: QQ.t ->
    'a context -> 'a arith_term array ->
    'a lira_to_polyhedron_abs

  val cch_lra:
    man:DD.closed Apron.Manager.t -> 'a context -> 'a arith_term array ->
    'a lira_to_polyhedron_abs

  (** All symbols must be of integer type.
      Local-project-local-hull is (sound and) compact when these conditions hold.
   *)
  val cch_lia:
    man:DD.closed Apron.Manager.t -> 'a context -> 'a arith_term array ->
    'a lira_to_polyhedron_abs

end = struct

  let default_epsilon = QQ.of_frac 1 10

  let restrict target_dim m dim =
    if dim < 0 || dim >= target_dim then
      invalid_arg (Format.asprintf "dimension %d cannot be interpreted" dim)
    else m dim

  type 'a lira_to_polyhedron_abs =
    ('a formula, 'a Interpretation.interpretation, DD.closed DD.t, (int -> QQ.t))
    local_abstraction

  let cch_lira ~man ?(epsilon=default_epsilon) srk terms =
    let (cubify, _) = Plt.cubify srk terms in
    let max_dim_in_target = Array.length terms - 1 in
    fun (plt, m) ->
      cubify (plt, m)
      |> PltConvexHull.by_polyreccone_and_lplh ~man ~epsilon ~max_dim_in_target

  let ddify ~man ambient_dim =
    (fun (p, m) -> P.dd_of ~man ambient_dim p, m)

  let cch_lra ~man srk terms =
    let (cubify, _) = Plt.cubify srk terms in
    let elim dim = dim >= Array.length terms in
    fun (plt, m) ->
      cubify (plt, m)
      |> CloseStrictIneq.round_assuming_no_ints
      |> LwCooper.real_local_project ~elim
      |> ddify ~man (Array.length terms)

  let _cch_lra_hull_then_project ~man srk terms =
    let project =
      let abstract p =
        let max_dim_in_p = P.max_constrained_dim p in
        let dimensions_to_eliminate =
          BatEnum.(Array.length terms -- max_dim_in_p) |> BatList.of_enum
        in
        P.project_dd dimensions_to_eliminate p
        |> P.dd_of ~man (Array.length terms)
      in
      fun (p, m) ->
        ( abstract p
        , restrict (Array.length terms) m
        )
    in
    let (cubify, _) = Plt.cubify srk terms in
    fun (plt, m) ->
      cubify (plt, m)
      |> CloseStrictIneq.round_assuming_no_ints
      |> project

  let cch_lia ~man srk terms =
    let (cubify, _) = Plt.cubify srk terms in
    let target_dim = Array.length terms in
    let elim dim = dim >= Array.length terms in
    fun (plt, m) ->
      cubify (plt, m)
      |> CloseStrictIneq.round_assuming_all_ints
      |> LwCooper.local_project ~elim
      |> LocalHull.local_hull ~man ~ambient_dim:target_dim

  (*  This isn't exposed right now because input formulas are in core LIRA where
      [is_int] atoms can be present. "Global" integer hull algorithms assume
      formulas are in the language of LRA, so we need to purify [is_int] atoms.
      [cch_lia] should be better most of the time, and handles [is_int] directly.
  *)
  let _cch_lia_hull_then_project hull_alg ~man srk terms =
    let target_dim = Array.length terms in
    let project =
      let abstract plt _m =
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
      fun (plt, m) ->
        ( abstract plt m
        , restrict target_dim m
        )
    in
    let (cubify, _) = Plt.cubify srk terms in
    fun (plt, m) ->
      cubify (plt, m)
      |> CloseStrictIneq.round_assuming_all_ints
      |> project
end

let _formula_of_plt = Plt.formula_of_plt

let select_vt = LwCooper.select_vt
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
