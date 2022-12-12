open Syntax
open BatPervasives

module V = Linear.QQVector
module CS = CoordinateSystem
module IntSet = SrkUtil.Int.Set
module IntMap = SrkUtil.Int.Map

type constraint_kind = [`Zero | `Nonneg | `Pos] [@@deriving ord]
type generator_kind = [`Vertex | `Ray | `Line]

include Log.Make(struct let name = "srk.polyhedron" end)

(* Replace x with replacement in term. *)
let replace_term x replacement term =
  let (a, t) = V.pivot x term in
  V.add (V.scalar_mul a replacement) t

module P = struct
  include BatSet.Make(struct
      type t = (constraint_kind * V.t) [@@deriving ord]
    end)

  let bottom =
    singleton (`Zero, Linear.const_linterm (QQ.of_int 1))

  let is_bottom = mem (`Zero, Linear.const_linterm (QQ.of_int 1))

  let top = empty

  let add (p, v) set =
    match Linear.const_of_linterm v with
    | Some value ->
      begin match p with
        | `Zero when QQ.equal QQ.zero value -> set
        | `Nonneg when QQ.leq QQ.zero value -> set
        | `Pos when QQ.lt QQ.zero value -> set
        | _ -> bottom
      end
    | None -> add (p, v) set

  let replace x replacement set =
    BatEnum.fold (fun set (p, t) ->
        add (p, replace_term x replacement t) set)
      empty
      (enum set)
end

type t = P.t

let enum_constraints polyhedron = P.enum polyhedron

let pp pp_dim formatter polyhedron =
  let pp_elt formatter = function
    | (`Zero, t) -> Format.fprintf formatter "%a = 0" (V.pp_term pp_dim) t
    | (`Nonneg, t) -> Format.fprintf formatter "%a >= 0" (V.pp_term pp_dim) t
    | (`Pos, t) -> Format.fprintf formatter "%a > 0" (V.pp_term pp_dim) t
  in
  let pp_sep formatter () = Format.fprintf formatter "@;" in
  Format.fprintf formatter "@[<v 0>%a@]"
    (SrkUtil.pp_print_enum_nobox ~pp_sep pp_elt) (P.enum polyhedron)

let of_dd polyhedron =
  BatEnum.fold (fun p cnstr -> P.add cnstr p) P.top (DD.enum_constraints polyhedron)

let dd_of ?(man=Polka.manager_alloc_loose ()) dim polyhedron =
  DD.of_constraints_closed ~man dim (P.enum polyhedron)

let nnc_dd_of ?(man=Polka.manager_alloc_strict ()) dim polyhedron =
  DD.of_constraints ~man dim (P.enum polyhedron)

let top = P.top
let bottom = P.bottom

let meet x y =
  if P.is_bottom x || P.is_bottom y then
    bottom
  else
    P.union x y

let of_formula ?(admit=false) cs phi =
  let linearize = CS.vec_of_term ~admit cs in
  let alg = function
    | `Tru -> top
    | `Fls -> bottom
    | `And xs -> List.fold_left meet top xs
    | `Atom (`Arith (`Eq, x, y)) ->
      P.singleton (`Zero, V.sub (linearize y) (linearize x))
    | `Atom (`Arith (`Leq, x, y)) ->
      P.singleton (`Nonneg, V.sub (linearize y) (linearize x))
    | `Atom (`Arith (`Lt, x, y)) ->
      P.singleton (`Pos, V.sub (linearize y) (linearize x))
    | `Or _ | `Not _ | `Quantify (_, _, _, _) | `Proposition _
    | `Ite (_, _, _) | `Atom (`ArrEq _)
    | `Atom (`IsInt _) -> invalid_arg "Polyhedron.of_formula"
  in
  Formula.eval (CS.get_context cs) alg phi

let implicant_of cs polyhedron =
  let srk = CS.get_context cs in
  let zero = mk_real srk QQ.zero in
  let term = CS.term_of_vec cs in
  P.fold (fun (p, t) constraints ->
      let new_constraint =
        match p with
        | `Zero -> mk_eq srk (term t) zero
        | `Nonneg -> mk_leq srk zero (term t)
        | `Pos -> mk_lt srk zero (term t)
      in
      new_constraint::constraints)
    polyhedron
    []

let to_formula cs polyhedron =
  implicant_of cs polyhedron
  |> mk_and (CS.get_context cs)

(* Check whether a given point belongs to a polyhedron *)
let mem m polyhedron =
  P.for_all (function
      | (`Zero, t) -> QQ.equal (Linear.evaluate_affine m t) QQ.zero
      | (`Nonneg, t) -> QQ.leq QQ.zero (Linear.evaluate_affine m t)
      | (`Pos, t) -> QQ.lt QQ.zero (Linear.evaluate_affine m t))
    polyhedron

let of_implicant ?(admit=false) cs conjuncts =
  let srk = CS.get_context cs in
  let linearize atom = match Interpretation.destruct_atom srk atom with
    | `ArithComparison (p, x, y) ->
      let t =
        V.sub (CS.vec_of_term ~admit cs y) (CS.vec_of_term ~admit cs x)
      in
      let p = match p with `Eq -> `Zero | `Leq -> `Nonneg | `Lt -> `Pos in
      P.singleton (p, t)
    | `Literal (_, _) -> top
    | `ArrEq _ -> top
  in
  List.fold_left meet top (List.map linearize conjuncts)

(* Given a coordinate x and a polyhedron p, find a term t such that p |= x=t
   and x does not appear in t, should one exist. *)
let select_equal_term x polyhedron =
  let enum = P.enum polyhedron in
  let rec go () = match BatEnum.get enum with
    | None -> None
    | Some (`Zero, t) ->
      let (a, t) = V.pivot x t in
      if QQ.equal a QQ.zero then
        go ()
      else
        Some (V.scalar_mul (QQ.inverse (QQ.negate a)) t)
    | Some (_, _) -> go ()
  in
  go ()

(* Loos-Weispfenning virtual term *)
type lw_vt =
  | MinusInfinity
  | PlusEpsilon of V.t
  | Term of V.t

(* Model-based selection of a Loos-Weispfenning virtual term *)
let select_lw m x polyhedron =
  match select_equal_term x polyhedron with
  | Some t -> Term t
  | None ->
    (* Internally to this function, it's convenient to represent a virtual
       term as a triple consisting of a term, its value in the model, and a
       flag indicating whether an epsilon is required (-oo is represented by
       None). *)
    let merge_vt_internal x y =
      match x, y with
      | None, x | x, None -> x
      | Some (_, value, _), Some (_, value', _) when QQ.lt value value' -> y
      | Some (_, value, _), Some (_, value', _) when QQ.lt value' value -> x
      | Some (_, _, _), Some (_, _, true) -> y
      | _, _ -> x
    in
    let vt_internal =
      P.fold (fun (p, t) vt ->
          let (a, t) = V.pivot x t in
          if QQ.leq a QQ.zero then
            vt
          else
            (* ax + t >= 0 /\ a > 0 |= x >= t/a *)
            let toa = V.scalar_mul (QQ.inverse (QQ.negate a)) t in
            let strict = (p = `Pos) in
            let value = Linear.evaluate_affine m toa in
            merge_vt_internal vt (Some (toa, value, strict)))
        polyhedron
        None
    in
    match vt_internal with
    | None -> MinusInfinity
    | Some (t, _, true) -> PlusEpsilon t
    | Some (t, _, false) -> Term t

let substitute_lw_vt x vt polyhedron =
  match vt with
  | Term t -> P.replace x t polyhedron
  | MinusInfinity ->
    P.fold (fun (p, term) polyhedron ->
        let a = V.coeff x term in
        if QQ.equal QQ.zero a then
          P.add (p, term) polyhedron
        else if QQ.lt QQ.zero a || p = `Zero then
          bottom
        else
          polyhedron)
      polyhedron
      top
  | PlusEpsilon t ->
    P.fold (fun (p, term) polyhedron ->
        let (a, term') = V.pivot x term in
        if QQ.equal QQ.zero a then
          P.add (p, term) polyhedron
        else
          let term' = V.add (V.scalar_mul a t) term' in
          if p = `Zero then
            bottom
          else if QQ.lt QQ.zero a then
            P.add (`Nonneg, term') polyhedron
          else
            P.add (`Pos, term') polyhedron)
      polyhedron
      top

(* Model-guided projection of a polyhedron.  Given a point m within a
   polyhedron p and a set of dimension xs, compute a polyhedron q such that
   m|_xs is within q, and q is a subset of p|_xs (using |_xs to denote
   projection of dimensions xs) *)
let local_project m xs polyhedron =
  (* Project a single variable *)
  let project_one polyhedron x =
    let vt = select_lw m x polyhedron in
    substitute_lw_vt x vt polyhedron
  in
  List.fold_left project_one polyhedron xs

(* Project a single variable, as long as the number of added constraints does
   not exceed max_add. If max_add is negative, the variable is projected no
   matter how many constraints it adds. *)
let project_one max_add polyhedron x =
  match select_equal_term x polyhedron with
  | Some t -> P.replace x t polyhedron
  | None ->
    (* If no equations involve x, find a least upper bound or greatest lower
       bound for x *)
    let (lower, upper, rest) =
      P.fold (fun (p, t) (lower, upper, rest) ->
          let (a, t) = V.pivot x t in
          if QQ.equal a QQ.zero then
            (lower, upper, P.add (p,t) rest)
          else
            let bound =
              (p = `Pos, V.scalar_mul (QQ.inverse (QQ.negate a)) t)
            in
            (* constraint is a*x + t >= 0, which is either x <= bound or bound
               <= x, depending on the sign of a *)
            if QQ.lt QQ.zero a then
              (bound::lower, upper, rest)
            else
              (lower, bound::upper, rest))
        polyhedron
        ([], [], top)
    in
    let nb_lower = List.length lower in
    let nb_upper = List.length upper in
    if max_add < 0 || max_add > (nb_lower*nb_upper-nb_lower-nb_upper) then
      List.fold_left (fun polyhedron (strict, lo) ->
          List.fold_left (fun polyhedron (strict', hi) ->
              if strict || strict' then
                P.add (`Pos, V.sub hi lo) polyhedron
              else
                P.add (`Nonneg, V.sub hi lo) polyhedron)
            polyhedron
            upper)
        rest
        lower
    else
      polyhedron

let project xs polyhedron =
  Log.time "Fourier-Motzkin" (List.fold_left (project_one (-1)) polyhedron) xs

exception Nonlinear
let to_apron cs env man polyhedron =
  let open SrkApron in
  let symvec v =
    V.enum v
    /@ (fun (coeff, coord) ->
        if coord == Linear.const_dim then
          (coeff, coord)
        else
          match CS.destruct_coordinate cs coord with
          | `App (sym, []) -> (coeff, int_of_symbol sym)
          | _ -> raise Nonlinear)
    |> V.of_enum
  in
  (* In the common case that the polyhedron is over a coordinate system
     without non-linear terms, it's faster to construct the apron abstract
     value from linear constraints; fall back on tree constraints when
     necessary. *)
  let (linear, nonlinear) =
    P.fold (fun (p, t) (linear, nonlinear) ->
        try
          let c =
            match p with
            | `Zero -> lcons_eqz (lexpr_of_vec env (symvec t))
            | `Nonneg -> lcons_geqz (lexpr_of_vec env (symvec t))
            | `Pos -> lcons_gtz (lexpr_of_vec env (symvec t))
          in
          (c::linear, nonlinear)
        with Nonlinear ->
          let c =
            match p with
            | `Zero -> tcons_eqz (texpr_of_term env (CS.term_of_vec cs t))
            | `Nonneg -> tcons_geqz (texpr_of_term env (CS.term_of_vec cs t))
            | `Pos -> tcons_gtz (texpr_of_term env (CS.term_of_vec cs t))
          in
          (linear, c::nonlinear)
      )
      polyhedron
      ([], [])
  in
  match nonlinear with
  | [] -> meet_lcons (top man env) linear
  | _ -> meet_tcons (meet_lcons (top man env) linear) nonlinear

let try_fourier_motzkin cs p polyhedron =
  let projected_linear =
    BatEnum.fold (fun remove i ->
        match CS.destruct_coordinate cs i with
        | `App (sym, []) -> if p sym then remove else IntSet.add i remove
        | _ ->
          IntSet.diff remove (CS.direct_subcoordinates cs i))
      IntSet.empty
      (0 -- (CS.dim cs - 1))
    |> IntSet.elements
  in
  Log.time "Fourier-Motzkin"
    (List.fold_left (project_one 10) polyhedron) projected_linear

(* All dimensions involved in a constraint. *)
let _constrained_dimensions polyhedron =
  BatEnum.fold (fun dims (_, v) ->
      BatEnum.fold (fun dims (_, dim) ->
          if dim == Linear.const_dim then
            dims
          else
            IntSet.add dim dims)
        dims
        (V.enum (snd (V.pivot Linear.const_dim v))))
    IntSet.empty
    (enum_constraints polyhedron)

let max_constrained_dim polyhedron =
  BatEnum.fold (fun dims (_, v) ->
      BatEnum.fold (fun max_dim (_, dim) -> max max_dim dim) dims (V.enum v))
    0
    (enum_constraints polyhedron)

let project_dd xs polyhedron =
  let dim = 1 + max_constrained_dim polyhedron in
  let polyhedron =
    List.fold_left (project_one 10) polyhedron xs
  in
  of_dd (DD.project xs (dd_of dim polyhedron))

let dual_cone dim polyhedron =
  (* Given polyhedron Ax >= b, form the constraint system
     lambda * A = y /\ lambda * b >= 0.
     Then project out the lambda dimensions.
  *)
  (* map [0 .. nb_constraints] to [dim .. dim + nb_constraints] *)
  assert (dim >= max_constrained_dim polyhedron);
  let lambda i = dim + i in
  let lambda_nonnegative =
    BatEnum.foldi
      (fun i (cmp, _) constraints ->
         match cmp with
         | `Zero -> constraints
         | `Nonneg | `Pos ->
           P.add (`Nonneg, V.of_term QQ.one (lambda i)) constraints)
      P.top
      (P.enum polyhedron)
  in
  let farkas_constraints =
    let zero =
      BatEnum.fold
        (fun map dim -> IntMap.add dim (V.of_term (QQ.of_int (-1)) dim) map)
        IntMap.empty
        (0 -- (dim - 1))
    in
    let (lambdaA, lambdab) =
      BatEnum.foldi
        (fun i (_, t) (lambdaA, lambdab) ->
           BatEnum.fold
             (fun (lambdaA, lambdab) (scalar, dim) ->
                if dim == Linear.const_dim then
                  (lambdaA, V.add_term (QQ.negate scalar) (lambda i) lambdab)
                else
                  (IntMap.modify dim (V.add_term scalar (lambda i)) lambdaA, lambdab))
             (lambdaA, lambdab)
             (V.enum t))
        (zero, V.zero)
        (P.enum polyhedron)
    in
    IntMap.fold (fun _ t constraints ->
        P.add (`Zero, t) constraints)
      lambdaA
      (P.add (`Nonneg, lambdab) lambda_nonnegative)
  in
  project
    (BatList.of_enum (dim -- (P.cardinal polyhedron + dim - 1)))
    farkas_constraints

let of_constraints constraints =
  BatEnum.fold (fun p constr -> P.add constr p) P.top constraints

(** Given a matrix [M] and a polyhedron [p], find a polyhedron [q]
    such that [p] contains a point [x] iff [q] contains [Mx].  Such a
    polyhedron exists iff [p] can be written as [Ax >= b], with the
    rowspace of [A] contained in the rowspace of [M]. *)
let invertible_image mM polyhedron =
  let mMt = Linear.QQMatrix.transpose mM in
  let densify_vec vec =
    let (a, vec) = V.pivot Linear.const_dim vec in
    match Linear.solve mMt vec with
    | Some v -> V.add_term a Linear.const_dim v
    | None -> invalid_arg "Densify: polyhedron is unrepresentible in the chosen basis"
  in
  P.fold (fun (kind, vec) dense ->
      P.add (kind, densify_vec vec) dense)
    polyhedron
    P.top

let conical_hull polyhedron =
  let dim = (max_constrained_dim polyhedron + 1) in
  dual_cone dim polyhedron
  |> dd_of dim
  |> DD.enum_generators
  |> BatEnum.filter_map (function
      | `Vertex, vec ->
        assert (V.equal V.zero vec);
        None
      | `Ray, vec ->
        Some (`Nonneg, vec)
      | `Line, vec ->
        Some (`Zero, vec))
  |> of_constraints

let constraint_space polyhedron =
  enum_constraints polyhedron
  /@ (fun (_, v) -> snd (V.pivot Linear.const_dim v))
  |> BatList.of_enum
  |> Linear.QQVectorSpace.basis

let equal p q =
  let man = Polka.manager_alloc_strict () in
  let cs = constraint_space p in
  let dim = List.length cs in
  let csM = Linear.QQVectorSpace.matrix_of cs in
  if Linear.QQVectorSpace.equal cs (constraint_space q) then
    let p0 = nnc_dd_of ~man dim (invertible_image csM p) in
    let q0 = nnc_dd_of ~man dim (invertible_image csM q) in
    DD.equal p0 q0
  else
    false

let valid_cone polyhedron =
  let dim = max_constrained_dim polyhedron in
  let (lines, rays) =
    P.fold (fun (p, v) (lines, rays) ->
        match p with
        | `Zero -> (v::lines, rays)
        | `Nonneg | `Pos -> (lines, v::rays))
      polyhedron
      ([], [V.of_term QQ.one Linear.const_dim])
  in
  Cone.make ~lines ~rays dim

let implies polyhedron (p, v) =
  let c = valid_cone polyhedron in
  match p with
  | `Zero -> Cone.mem v c && Cone.mem (V.negate v) c
  | `Nonneg -> Cone.mem v c
  | `Pos -> invalid_arg "Polyhedron.implies does not currently support strict \
                         inequalities"

module NormalizCone = struct

  open Normalizffi

  (* Rescale vector such that the selected coefficients are integral and
     relatively prime *)
  let normalize v =
    Linear.QQVector.scalar_mul (QQ.inverse (Linear.QQVector.gcd_entries v)) v

  module D = Linear.MakeDenseConversion(SrkUtil.Int)(V)

  let densify ctx v =
    let array = Array.make (D.dim ctx) (ZZ.mpz_of ZZ.zero) in
    BatEnum.iter
      (fun (a, i) ->
         array.(D.int_of_dim ctx i) <- ZZ.mpz_of (Option.get (QQ.to_zz a)))
      (V.enum v);
    Array.to_list array

  let sparsify ctx v =
    BatList.fold_lefti (fun vec i a ->
        V.set (D.dim_of_int ctx i) (QQ.of_zz (ZZ.of_mpz a)) vec)
      V.zero
      v

  let normaliz_cone_by_constraints polyhedron =
    let normalized_constraints =
      enum_constraints polyhedron
      /@ (fun (p, v) -> (p, normalize v))
      |> (* Add 1 >= 0 to ensure the constant dimension x0 is present,
            so that the cone may be dehomogenized at x0 = 1 if needed
            to get a polyhedron.
         *)
      (fun enum ->
         BatEnum.push enum (`Nonneg, Linear.const_linterm (QQ.of_int 1)); enum)
      |> BatList.of_enum
    in
    let ctx =
      BatList.enum normalized_constraints
      /@ snd
      |> D.min_context
    in
    (* The constant dimension must be present and be the first coordinate *)
    assert (D.int_of_dim ctx Linear.const_dim = 0);
    let (equalities, inequalities) =
      List.fold_left
        (fun (equalities, inequalities) (kind, v) ->
           match kind with
           | `Zero -> (densify ctx v :: equalities, inequalities)
           | `Nonneg -> (equalities, densify ctx v :: inequalities)
           | `Pos -> invalid_arg "normaliz_cone_of: open faces not supported yet")
        ([], [])
        normalized_constraints in
    try
      let cone = Normaliz.empty_cone
                 |> Normaliz.add_equalities equalities |> Result.get_ok
                 |> Normaliz.add_inequalities inequalities |> Result.get_ok
                 |> Normaliz.new_cone
      in
      (cone, ctx)
    with Invalid_argument s -> logf "normaliz_cone_by_constraints"; invalid_arg s

  let polyhedron_of (equalities, inequalities, ctx) =
    let to_constraint kind v = (kind, sparsify ctx v) in
    let equalities = List.map (to_constraint `Zero) equalities in
    let inequalities = List.map (to_constraint `Nonneg) inequalities in
    BatList.enum (List.append equalities inequalities)
    |> of_constraints

  let integer_hull polyhedron =
    let (cone, bijection) = normaliz_cone_by_constraints polyhedron in

    logf ~level:`trace "polyhedron: integer_hull: computed Normaliz cone for polyhedron:@[%a@]@;"
      (pp (Polynomial.pp_numeric_dim "x")) polyhedron;

    let dehomogenized = Normaliz.dehomogenize cone in
    logf ~level:`trace "polyhedron: integer_hull: dehomogenized cone, computing integer hull...@;";
    Normaliz.hull dehomogenized;
    if !my_verbosity_level = `trace then
      logf ~level:`trace "polyhedron: integer_hull: computed integer hull: @[%a@]@;"
        Normaliz.pp_hull dehomogenized
    else ();

    let cut_ineqs = Normaliz.get_int_hull_inequalities dehomogenized in
    let cut_eqns = Normaliz.get_int_hull_equations dehomogenized
    in
    polyhedron_of (cut_eqns, cut_ineqs, bijection)

  (* [fractional_cutting_planes_at_face point active_constraints ambient_dim]
     returns pairs [constraint >= constant], such that
     [constraint = constant] is a cutting plane of the polyhedron in 
     QQ^{[ambient_dim]} defined by [active_constraints] and contains [point],
     and where [constant] is non-integer (so that the cutting plane makes 
     progress when cut).
  *)
  let fractional_cutting_planes_at_face
      point
      (active : (constraint_kind * V.t) BatEnum.t)
      ambient_dim
    : (V.t * QQ.t) BatEnum.t option =
    if V.is_integral point then
      None
    else
      let (lines, rays) =
        let strip_constant = snd % V.pivot Linear.const_dim in
        BatEnum.fold (fun (lines, rays) -> function
            | (`Zero, v) -> (strip_constant v :: lines, rays)
            | (`Nonneg, v) -> (lines, strip_constant v :: rays)
            | (`Pos, _v) -> assert false)
          ([], [])
          active
      in
      let basis = Cone.hilbert_basis (Cone.make ~lines ~rays ambient_dim) in
      Some (basis
            |> BatList.fold_left
              (fun curr vector ->
                 let constant_term = Linear.QQVector.dot vector point in
                 if ZZ.equal (QQ.denominator constant_term) ZZ.one then
                   curr
                 else
                   (vector, constant_term) :: curr) []
            |> BatList.enum
           )

  let elementary_gc polyhedron ambient_dim =
    logf ~level:`trace "elementary_gc: Computing minimal faces...@;";
    let faces = DD.minimal_faces polyhedron in
    logf ~level:`trace "elementary_gc: Computed minimal faces: found %d@;"
      (List.length faces);
    let cuts =
      List.fold_left (fun curr (v, active) ->
          let frac_cuts = fractional_cutting_planes_at_face v (BatList.enum active) ambient_dim in
          match frac_cuts with
          | None -> curr
          | Some cuts ->
            BatEnum.push curr (v, cuts);
            curr)
        (BatEnum.empty ())
        faces
    in
    if BatEnum.is_empty cuts then
      begin
        logf "elementary_gc: all faces are integral@;";
        `Fixed polyhedron
      end
    else
      let changed = ref false in
      let adjoin_constraint curr_polyhedron (lhs, rhs) =
        (* TODO: Test if meet is faster than implication check; if so,
             we should do meet directly once [changed] is true.
        *)
        let constant_term = QQ.negate rhs |> QQ.floor |> QQ.of_zz in
        let new_constraint =
          Linear.QQVector.add_term constant_term Linear.const_dim lhs in
        if DD.implies curr_polyhedron (`Nonneg, new_constraint) then
          begin
            logf ~level:`trace "@[elementary_gc: polyhedron implies %a >= 0@]@;"
              Linear.QQVector.pp new_constraint;
            curr_polyhedron
          end
        else
          begin
            logf ~level:`trace "@[elementary_gc: computing meet with %a >= 0@]@;"
              Linear.QQVector.pp new_constraint;
            let intersected = DD.meet_constraints
                curr_polyhedron [(`Nonneg, new_constraint)] in
            changed := true;
            intersected
          end
      in
      let polyhedron =
        BatEnum.fold (fun poly (_point, cutting_planes) ->
            BatEnum.fold adjoin_constraint poly cutting_planes)
          polyhedron cuts
      in
      if !changed then `Changed polyhedron else `Fixed polyhedron

  let gomory_chvatal polyhedron =
    let dim = 1 + max_constrained_dim polyhedron in
    let man = Polka.manager_alloc_loose () in
    let rec iter polyhedron i =
      let elem_closure =  elementary_gc polyhedron dim in
      match elem_closure with
      | `Fixed poly ->
        logf ~level:`info "@[Polyhedron: Gomory-Chvatal finished in round %d@]@;" i;
        poly
      | `Changed poly ->
        logf ~level:`trace "elementary_gc: entering round %d@;" (i + 1);
        iter poly (i + 1)
    in
    iter (dd_of ~man dim polyhedron) 0
    |> of_dd

end

let integer_hull = function
  | `GomoryChvatal -> NormalizCone.gomory_chvatal
  | `Normaliz -> NormalizCone.integer_hull

module IntDS = DisjointSet.Make(struct
    include Int
    let hash = Hashtbl.hash
    let equal = (=)
  end)

let factor polyhedron =
  let ds = IntDS.create 991 in
  enum_constraints polyhedron |> BatEnum.iter
    (fun (_, v) ->
       let ((i, _), v') = V.pop (snd (V.pivot Linear.const_dim v)) in
       let rep = IntDS.find ds i in
       V.enum v' |> BatEnum.iter (fun (_, j) ->
           ignore (IntDS.union (IntDS.find ds j) rep)));
  let rev_map =
    IntDS.reverse_map ds IntSet.empty IntSet.add
  in
  let find_rep i = IntSet.choose (rev_map i) in
  let map =
    BatEnum.fold (fun map (kind, vec) ->
        let equiv_class =
          find_rep (fst (fst (V.pop (snd (V.pivot Linear.const_dim vec)))))
        in
        IntMap.modify_def P.top equiv_class (P.add (kind, vec)) map)
      IntMap.empty
      (enum_constraints polyhedron)
  in
  BatList.of_enum (IntMap.values map)

let integer_hull ?(decompose=true) how =
  Log.time "Integer hull" (fun p ->
      if decompose then
        List.fold_left
          (fun rest factor -> meet rest (integer_hull how factor))
          top
          (factor p)
      else
        integer_hull how p)
