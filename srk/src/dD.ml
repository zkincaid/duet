open Apron
open BatPervasives

module V = Linear.QQVector

type constraint_kind = [`Zero | `Nonneg | `Pos]
type generator_kind = [`Vertex | `Ray | `Line]
type 'a t = 'a Abstract0.t

type closed = Polka.loose Polka.t
type nnc = Polka.strict Polka.t

let ambient_dimension t = (Abstract0.dimension (Abstract0.manager t) t).reald

let pp_constraint fmt = function
  | (`Zero, v) -> Format.fprintf fmt "%a = 0" Linear.QQVector.pp v
  | (`Nonneg, v) -> Format.fprintf fmt "%a >= 0" Linear.QQVector.pp v
  | (`Pos, v) -> Format.fprintf fmt "%a > 0" Linear.QQVector.pp v

include Log.Make(struct let name = "srk.DD" end)

let lexpr_of_vec vec =
  let mk (coeff, dim) = (SrkApron.coeff_of_qq coeff, dim) in
  let (const_coeff, rest) = V.pivot Linear.const_dim vec in
  Apron.Linexpr0.of_list None
    (BatList.of_enum (BatEnum.map mk (V.enum rest)))
    (Some (SrkApron.coeff_of_qq const_coeff))

let vec_of_lexpr linexpr =
  let vec = ref V.zero in
  Linexpr0.iter (fun coeff dim ->
      match SrkApron.qq_of_coeff coeff with
      | Some qq -> vec := V.add_term qq dim (!vec)
      | None -> assert false)
    linexpr;
  match SrkApron.qq_of_coeff (Linexpr0.get_cst linexpr) with
  | Some qq -> V.add_term qq Linear.const_dim (!vec)
  | None -> assert false

let lcons_of_constraint (cmp, vec) =
  let cmp = match cmp with
    | `Zero -> Lincons0.EQ
    | `Pos -> Lincons0.SUP
    | `Nonneg -> Lincons0.SUPEQ
  in
  Lincons0.make (lexpr_of_vec vec) cmp

let constraint_of_lcons lcons =
  let open Lincons0 in
  let cmp = match lcons.typ with
    | Lincons0.EQ -> `Zero
    | Lincons0.SUP -> `Pos
    | Lincons0.SUPEQ -> `Nonneg
    | _ -> assert false
  in
  (cmp, vec_of_lexpr lcons.linexpr0)

let project xs polyhedron =
  Abstract0.forget_array
    (Abstract0.manager polyhedron)
    polyhedron
    (Array.of_list xs)
    false

let enum_generators polyhedron =
  let open Apron in
  Abstract0.to_generator_array (Abstract0.manager polyhedron) polyhedron
  |> BatArray.enum
  |> BatEnum.filter_map Generator0.(fun g ->
      let vec = vec_of_lexpr g.linexpr0 in
      match g.typ with
      | LINE -> Some (`Line, vec)
      | RAY -> Some (`Ray, vec)
      | VERTEX -> Some (`Vertex, vec)
      | LINEMOD | RAYMOD -> assert false)

let enum_constraints polyhedron =
  Abstract0.to_lincons_array (Abstract0.manager polyhedron) polyhedron
  |> BatArray.enum
  |> BatEnum.map constraint_of_lcons

let enum_constraints_closed polyhedron =
  Abstract0.to_lincons_array (Abstract0.manager polyhedron) polyhedron
  |> BatArray.enum
  |> BatEnum.map (fun lcons ->
      match constraint_of_lcons lcons with
      | (`Pos, _) -> assert false
      | (`Zero, v) -> `Zero, v
      | (`Nonneg, v) -> `Nonneg,v)

let pp pp_dim formatter polyhedron =
  let pp_elt formatter = function
    | (`Zero, t) -> Format.fprintf formatter "%a = 0" (V.pp_term pp_dim) t
    | (`Nonneg, t) -> Format.fprintf formatter "%a >= 0" (V.pp_term pp_dim) t
    | (`Pos, t) -> Format.fprintf formatter "%a > 0" (V.pp_term pp_dim) t
  in
  let pp_sep formatter () = Format.fprintf formatter "@;" in
  Format.fprintf formatter "@[<v 0>%a@]"
    (SrkUtil.pp_print_enum_nobox ~pp_sep pp_elt) (enum_constraints polyhedron)

let equal p q = Abstract0.is_eq (Abstract0.manager p) p q
let join p q = Abstract0.join (Abstract0.manager p) p q
let meet p q = Abstract0.meet (Abstract0.manager p) p q

let of_generators ?(man=Polka.manager_alloc_loose ()) dim generators =
  let open Apron in
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

  let implies polyhedron cons =
    Abstract0.sat_lincons
      (Abstract0.manager polyhedron)
      polyhedron
      (lcons_of_constraint cons)

  let meet_constraints polyhedron cons =
    Apron.Abstract0.meet_lincons_array
      (Abstract0.manager polyhedron)
      polyhedron
      (Array.of_list (List.map lcons_of_constraint cons))

let minimal_faces polyhedron : (V.t * ((constraint_kind * V.t) list)) list =
  let satisfied coeffs point =
    let homogenized_point = Linear.QQVector.add_term QQ.one Linear.const_dim point in
    QQ.equal (Linear.QQVector.dot coeffs homogenized_point) QQ.zero in
  let defining_equations_for v =
    let constraints =
      enum_constraints polyhedron
      //@ (function
          | (`Zero, u) -> if satisfied u v then Some (`Zero, u) else None
          | (`Nonneg, u) -> if satisfied u v then Some (`Nonneg, u) else None
          | (`Pos, _) -> None)
      |> BatList.of_enum
    in
    (v, constraints)
  in
  let log_face (v, defining) =
    logf ~level:`trace "minimal face: vertex: @[%a@]@;defining constraints: @[%a@]"
      Linear.QQVector.pp v
      (fun fmt constraints ->
         List.iter (Format.fprintf fmt "%a@;" pp_constraint) constraints)
      defining in
  logf ~level:`trace "@[minimal_face: minimal faces of polyhedron @[%a@]@]"
    (pp (fun fmt i -> Format.fprintf fmt ":%d" i)) polyhedron;
  enum_generators polyhedron
  //@ (function
      | (`Vertex, v) -> Some v
      | _ -> None)
  |> BatList.of_enum
  |> List.map defining_equations_for
  |> (function defining ->
      List.iter log_face defining;
      defining)

module IntegerHull = struct

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

  (* TODO: This is basically Cone's [hilbert_basis] function, but there is
     a dependency cycle between Cone and DD.
   *)
  let hilbert_basis lines rays =
    let open Normalizffi in
    let normalize v =
      Linear.QQVector.scalar_mul (QQ.inverse (Linear.QQVector.gcd_entries v)) v in
    let lineality = List.map normalize lines in
    let rays = List.map normalize rays in
    let ctx = D.min_context (BatList.enum (lineality @ rays)) in
    let normaliz_rays =
      BatList.concat_map (fun line -> [line ; V.negate line]) lineality
      |> BatList.rev_append rays
      |> BatList.map (densify ctx)
    in
    let cone = Normaliz.empty_cone
               |> Normaliz.add_rays normaliz_rays |> Result.get_ok
               |> Normaliz.new_cone in
    let (pointed_hilbert_basis, lineality_basis) =
      (Normaliz.hilbert_basis cone,  Normaliz.get_lineality_space cone)
      |> (fun (l1, l2) ->
        let sparsify = List.map (sparsify ctx) in
        (sparsify l1, sparsify l2))
    in
    pointed_hilbert_basis
    @ lineality_basis
    @ List.map Linear.QQVector.negate lineality_basis

  (* [fractional_cutting_planes_at_face point active_constraints ambient_dim]
     returns pairs [constraint >= constant], such that
     [constraint = constant] is a cutting plane of the polyhedron in
     QQ^{[ambient_dim]} defined by [active_constraints] and contains [point],
     and where [constant] is non-integer (so that the cutting plane makes
     progress when cut).
   *)
  let fractional_cutting_planes_at_face
        point
        (active : (constraint_kind * V.t) BatEnum.t): (V.t * QQ.t) BatEnum.t option =
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
      let basis = hilbert_basis lines rays in
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

  let elementary_gc polyhedron =
    logf ~level:`trace "elementary_gc: Computing minimal faces...@;";
    let faces = minimal_faces polyhedron in
    logf ~level:`trace "elementary_gc: Computed minimal faces: found %d@;"
      (List.length faces);
    let cuts =
      List.fold_left (fun curr (v, active) ->
          let frac_cuts = fractional_cutting_planes_at_face v (BatList.enum active) in
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
        if implies curr_polyhedron (`Nonneg, new_constraint) then
          begin
            logf ~level:`trace "@[elementary_gc: polyhedron implies %a >= 0@]@;"
              Linear.QQVector.pp new_constraint;
            curr_polyhedron
          end
        else
          begin
            logf ~level:`trace "@[elementary_gc: computing meet with %a >= 0@]@;"
              Linear.QQVector.pp new_constraint;
            let intersected = meet_constraints
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
    let rec iter polyhedron i =
      let elem_closure =  elementary_gc polyhedron in
      match elem_closure with
      | `Fixed poly ->
         logf ~level:`info "@[Polyhedron: Gomory-Chvatal finished in round %d@]@;" i;
         poly
      | `Changed poly ->
         logf ~level:`trace "elementary_gc: entering round %d@;" (i + 1);
         iter poly (i + 1)
    in
    iter polyhedron 0
end

let integer_hull = IntegerHull.gomory_chvatal

let of_constraints ?(man=Polka.manager_alloc_strict ()) dim constraints =
  constraints
  /@ lcons_of_constraint
  |> BatArray.of_enum
  |> Abstract0.of_lincons_array man 0 dim

let of_constraints_closed ?(man=Polka.manager_alloc_loose ()) dim constraints =
  constraints
  /@ lcons_of_constraint
  |> BatArray.of_enum
  |> Abstract0.of_lincons_array man 0 dim
