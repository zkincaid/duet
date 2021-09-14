open Syntax
open BatPervasives

module V = Linear.QQVector
module CS = CoordinateSystem
module IntSet = SrkUtil.Int.Set
module IntMap = SrkUtil.Int.Map

type constraint_kind = [`Zero | `Nonneg | `Pos] [@@deriving ord]
type generator_kind = [`Vertex | `Ray | `Line]

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
    | `Ite (_, _, _) | `Atom (`ArrEq _) ->
      invalid_arg "Polyhedron.of_formula"
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

let lexpr_of_vec vec =
  let mk (coeff, dim) = (SrkApron.coeff_of_qq coeff, dim) in
  let (const_coeff, rest) = V.pivot Linear.const_dim vec in
  Apron.Linexpr0.of_list None
    (BatList.of_enum (BatEnum.map mk (V.enum rest)))
    (Some (SrkApron.coeff_of_qq const_coeff))

let vec_of_lexpr linexpr =
  let open Apron in
  let vec = ref V.zero in
  Linexpr0.iter (fun coeff dim ->
      match SrkApron.qq_of_coeff coeff with
      | Some qq -> vec := V.add_term qq dim (!vec)
      | None -> assert false)
    linexpr;
  match SrkApron.qq_of_coeff (Linexpr0.get_cst linexpr) with
  | Some qq -> V.add_term qq Linear.const_dim (!vec)
  | None -> assert false

let apron0_of man dim polyhedron =
  let open Apron in
  let lincons_of (cmp, vec) =
    let cmp = match cmp with
      | `Zero -> Lincons0.EQ
      | `Pos -> Lincons0.SUP
      | `Nonneg -> Lincons0.SUPEQ
    in
    Lincons0.make (lexpr_of_vec vec) cmp
  in
  P.enum polyhedron
  /@ lincons_of
  |> BatArray.of_enum
  |> Abstract0.of_lincons_array man 0 dim

let of_apron0 man abstract0 =
  let open Apron in
  let constraint_of lcons =
    let open Lincons0 in
    let cmp = match lcons.typ with
      | Lincons0.EQ -> `Zero
      | Lincons0.SUP -> `Pos
      | Lincons0.SUPEQ -> `Nonneg
      | _ -> assert false
    in
    (cmp, vec_of_lexpr lcons.linexpr0)
  in
  BatArray.fold_left
    (fun p lcons ->
      P.add (constraint_of lcons) p)
    P.top
    (Abstract0.to_lincons_array man abstract0)

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

let enum_generators dim polyhedron =
  let open Apron in
  let man = Polka.manager_alloc_loose () in
  polyhedron
  |> apron0_of man dim
  |> Abstract0.to_generator_array man
  |> BatArray.enum
  |> BatEnum.filter_map Generator0.(fun g ->
         let vec = vec_of_lexpr g.linexpr0 in
         match g.typ with
         | LINE -> Some (`Line, vec)
         | RAY -> Some (`Ray, vec)
         | VERTEX -> Some (`Vertex, vec)
         | LINEMOD | RAYMOD -> assert false)

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
  |> enum_generators dim
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
    let p0 = apron0_of man dim (invertible_image csM p) in
    let q0 = apron0_of man dim (invertible_image csM q) in
    Apron.Abstract0.is_eq man p0 q0
  else
    false

let of_generators dim generators =
  let open Apron in
  let man = Polka.manager_alloc_loose () in
  let (vertices, rays) =
    BatEnum.fold Generator0.(fun (vertices, rays) (kind, vec) ->
        match kind with
        | `Line -> (vertices, (make (lexpr_of_vec vec) LINE)::rays)
        | `Ray -> (vertices, (make (lexpr_of_vec vec) RAY)::rays)
        | `Vertex -> (vec::vertices, rays))
      ([], [])
      generators
  in
  let polytope_of_point point =
    Abstract0.of_lincons_array man 0 dim
      (Array.init dim (fun i ->
           (* x_i = point_i *)
           let lexpr =
             [(QQ.of_int (-1), i);
              (V.coeff i point, Linear.const_dim)]
             |> V.of_list
             |> lexpr_of_vec
           in
           Lincons0.make lexpr Lincons0.EQ))
  in
  let polytope = (* Convex hull of vertices *)
    BatList.reduce
      (Abstract0.join man)
      (List.map polytope_of_point vertices)
  in
  Abstract0.add_ray_array man polytope (BatArray.of_list rays)
  |> of_apron0 man
