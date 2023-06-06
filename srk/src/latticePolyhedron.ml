module V = Linear.QQVector
module P = Polyhedron
module T = Linear.MakeLinearMap(QQ)(Int)(V)(V)

include Log.Make(struct let name = "srk.latticePolyhedron" end)

let pp_linear_map fmt linear_map =
  BatEnum.iter (fun (s, t) ->
      Format.fprintf fmt "(%a, %a); " Linear.QQVector.pp s Linear.QQVector.pp t)
    (T.enum linear_map)

let force_transform (forward, inverse, num_dimensions) p =
  let q = BatEnum.empty () in
  let (forward, inverse, num_dimensions) =
    BatEnum.fold
      (fun (forward, inverse, num_dimensions) (kind, v) ->
        match T.apply forward v with
        | None ->
           let image = V.of_term QQ.one num_dimensions in
           BatEnum.push q (kind, image);
           let new_forward =
             match T.add v image forward with
             | Some forward' -> forward'
             | None ->
                logf ~level:`always
                  "force_transform forward: %a is already in the domain of %a@."
                  Linear.QQVector.pp v pp_linear_map forward;
                failwith "force_transform: forward extension conflict"
           in
           let new_backward =
             match T.add image v inverse with
             | Some backward' -> backward'
             | None ->
                logf ~level:`always
                  "force_transform inverse: %a is already in the domain of %a@."
                  Linear.QQVector.pp image pp_linear_map inverse;
                failwith "force_transform: inverse extension conflict"
           in
           ( new_forward, new_backward, num_dimensions + 1)
        | Some image ->
           BatEnum.push q (kind, image);
           (forward, inverse, num_dimensions)
      )
      (forward, inverse, num_dimensions)
      (P.enum_constraints p)
  in
  (forward, inverse, num_dimensions, P.of_constraints q)

let transform map p =
  let q = BatEnum.empty () in
  BatEnum.iter (fun (kind, v) ->
      match T.apply map v with
      | None -> failwith "transformation is malformed"
      | Some image ->
         BatEnum.push q (kind, image)
    )
    (P.enum_constraints p);
  P.of_constraints q

let pp_dim = fun fmt d -> Format.fprintf fmt "%d" d

let lattice_polyhedron_of p l =
  let basis = IntLattice.basis l in
  let (forward_l, inverse_l, num_dimensions_l) =
    List.fold_left (fun (forward, inverse, index) v ->
        let f = T.may_add v (V.of_term QQ.one index) forward in
        let b = T.may_add (V.of_term QQ.one index) v inverse in
        (f, b, index + 1))
      ( T.may_add (V.of_term QQ.one Linear.const_dim)
          (V.of_term QQ.one Linear.const_dim) T.empty
      , T.may_add (V.of_term QQ.one Linear.const_dim)
          (V.of_term QQ.one Linear.const_dim) T.empty
      , 0)
      basis
  in
  logf ~level:`trace "Transform computed so far is %a@." pp_linear_map forward_l;
  logf ~level:`trace
    "Forcing transform on polyhedron %a@." (Polyhedron.pp pp_dim) p;
  let (_forward, inverse, _num_dimensions, q) =
    force_transform (forward_l, inverse_l, num_dimensions_l) p
  in
  logf ~level:`trace "Forced transform, obtained %a@." (Polyhedron.pp pp_dim) q;
  let hull = Polyhedron.integer_hull `GomoryChvatal q in
  logf ~level:`trace "standard integer hull is %a@." (Polyhedron.pp pp_dim) hull;
  transform inverse hull
