module V = Linear.QQVector
module P = Polyhedron
module L = IntLattice
module T = Linear.MakeLinearMap(QQ)(Int)(V)(V)

include Log.Make(struct let name = "srk.latticePolyhedron" end)

let map_polyhedron map p =
  let q = BatEnum.empty () in
  BatEnum.iter (fun (kind, v) ->
      match T.apply map v with
      | None -> failwith "lattice is not full-dimensional"
      | Some image ->
         BatEnum.push q (kind, image)
    )
    (P.enum_constraints p);
  P.of_constraints q

let pp_dim = fun fmt d -> Format.fprintf fmt "%d" d

(* Compute the map [f] that sends [l] to a space where [f(l)] is the standard 
   lattice. *)
let make_map l =
  let basis = IntLattice.basis l in
  let map_one =
    let one = V.of_term QQ.one Linear.const_dim in
    T.may_add one one T.empty in
  let fresh_dim = ref 0 in
  let adjoin (f, b) v =
    let f' = T.may_add v (V.of_term QQ.one !fresh_dim) f in
    let b' = T.may_add (V.of_term QQ.one !fresh_dim) v b in
    fresh_dim := !fresh_dim + 1;
    (f', b')
  in
  let (forward, inverse) = List.fold_left adjoin (map_one, map_one) basis in
  (forward, inverse)

let lattice_polyhedron_of p l =
  let (forward, inverse) = make_map l in
  let q = map_polyhedron forward p in
  logf ~level:`trace "Polyhedron in %a@." (Polyhedron.pp pp_dim) q;
  let hull = Polyhedron.integer_hull `GomoryChvatal q in
  logf ~level:`trace "standard integer hull is %a@." (Polyhedron.pp pp_dim) hull;
  map_polyhedron inverse hull

module ModelBasedProjection : sig

  val local_project_cooper :
    (int -> QQ.t) -> eliminate:(int list) ->
    Polyhedron.t * IntLattice.t -> Polyhedron.t * IntLattice.t

end = struct

  let normalize a dim =
    let c = V.coeff dim a in
    if QQ.equal c QQ.zero then a
    else V.scalar_mul (QQ.inverse (QQ.abs c)) a

  let get_bound dim v =
    let drop_dim v = V.pivot dim v |> snd in
    if QQ.lt (V.coeff dim v) Q.zero then
      normalize v dim |> drop_dim
    else if QQ.lt Q.zero (V.coeff dim v) then
      normalize v dim |> drop_dim |> V.negate
    else
      failwith "Vector is 0 in the dimension"

  let evaluate_bound dim v m =
    Linear.evaluate_affine m (get_bound dim v)

  let substitute_term t dim v =
    let (c, v') = V.pivot dim v in
    V.add v' (V.scalar_mul c t)

  (* A classified system of constraints with respect to a chosen dimension x and
   a model m contains:
   - The row a^T Y + cx + b >= 0 (or = 0) that gives the glb, if one exists,
     where c is positive
   - All rows that involve x
   - All rows that don't involve x
   *)
  type classified =
    {
      glb_row : (QQ.t * P.constraint_kind * V.t) option
    ; relevant : (P.constraint_kind * V.t) BatEnum.t
    ; irrelevant : (P.constraint_kind * V.t) BatEnum.t
    }

  let classify_constraints m dim constraints =
    BatEnum.fold (fun (classified, upper_bound_seen) (kind, v) ->
        if QQ.equal (V.coeff dim v) QQ.zero then
          begin
            BatEnum.push classified.irrelevant (kind, v);
            (classified, upper_bound_seen)
          end
        else if QQ.lt (V.coeff dim v) QQ.zero then
          begin
            BatEnum.push classified.relevant (kind, v);
            (classified, true)
          end
        else
          begin
            BatEnum.push classified.relevant (kind, v);
            let value = evaluate_bound dim v m in
            match classified.glb_row with
            | None ->
               ({ classified with glb_row = Some (value, kind, v) }, upper_bound_seen)
            | Some (curr_best, curr_kind, _) ->
               if QQ.lt curr_best value ||
                    (QQ.equal curr_best value && curr_kind = `Nonneg && kind = `Pos) then
                 ({ classified with glb_row = Some (value, kind, v) }, upper_bound_seen)
               else
                 (classified, upper_bound_seen)
          end
      )
      ({
          glb_row = None
        ; relevant = BatEnum.empty ()
        ; irrelevant = BatEnum.empty ()
        }, false)
      constraints

  let pp_dim = fun fmt d -> Format.fprintf fmt "%d" d

  let local_project_cooper m ~eliminate (p, l) =
    BatList.fold_left (fun (p, l) dim ->
        let (classified, has_upper_bound) =
          classify_constraints m dim (P.enum_constraints p) in
        if not (has_upper_bound) || classified.glb_row = None then
          ( P.of_constraints classified.irrelevant
          , IntLattice.project (fun dim -> not (BatList.mem dim eliminate)) l )
        else
          let glb_term =
            let (_, _, glb_row) = Option.get classified.glb_row in
            get_bound dim glb_row
          in
          let divisor =
            BatList.fold_left
              (fun m v ->
                let coeff = Linear.QQVector.coeff dim v in
                if QQ.equal coeff QQ.zero then m
                else ZZ.lcm m (QQ.denominator coeff))
              ZZ.one
              (L.basis l)
          in
          let difference = QQ.sub (m dim) (Linear.evaluate_affine m glb_term) in
          let residue = QQ.modulo difference (QQ.of_zz divisor) in
          let solution = V.add_term residue Linear.const_dim glb_term in
          logf ~level:`trace "glb value %a <= point %a, difference %a, divisor %a, residue %a@."
            QQ.pp (Linear.evaluate_affine m glb_term) QQ.pp (m dim)
            QQ.pp difference QQ.pp (QQ.of_zz divisor) QQ.pp residue;
          logf ~level:`trace "glb term %a@." V.pp glb_term;
          logf ~level:`trace "selected term %a, <= %a:1@." V.pp solution pp_dim dim;
          let open BatEnum in
          let new_p =
            classified.relevant
            /@ (fun (kind, a) ->
              (kind, substitute_term solution dim a))
            |> BatEnum.append classified.irrelevant
            |> P.of_constraints in
          let new_l =
            List.map (substitute_term solution dim) (IntLattice.basis l)
            |> IntLattice.hermitize
          in
          (new_p, new_l)
      ) (p, l) eliminate

end

let local_project_cooper = ModelBasedProjection.local_project_cooper
