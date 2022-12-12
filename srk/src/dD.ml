open Apron
open BatPervasives

module V = Linear.QQVector

type constraint_kind = [`Zero | `Nonneg | `Pos]
type generator_kind = [`Vertex | `Ray | `Line]
type 'a t = 'a Abstract0.t

type closed = Polka.loose Polka.t
type nnc = Polka.strict Polka.t

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
