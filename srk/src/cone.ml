open BatPervasives

module V = Linear.QQVector
module M = Linear.QQMatrix
module VS = Linear.QQVectorSpace
module IntSet = SrkUtil.Int.Set
module IntMap = SrkUtil.Int.Map

include Log.Make(struct let name = "srk.cone" end)

(* QS represents a vector space L along with a function reduce that
   maps each vector in QQ^omega to its representative in the quotient
   QQ^omega/L.  Representatives are chosen to use as few dimensions as
   possible. *)
module QS = Linear.MakeLinearSpace(QQ)(SrkUtil.Int)(Linear.QQVector)

module MakeSolver
    (D : Map.OrderedType)
    (V : sig
       include Linear.SparseArray with type dim = D.t
                                   and type scalar = QQ.t
     end) = struct
  module QQV = Linear.QQVector
  module Map = Linear.MakeLinearMap(QQ)(D)(V)(QQV)
  module Fun = Linear.MakeLinearMap(QQ)(D)(V)(struct
      type scalar = QQ.t
      include QQ
      let is_zero = QQ.equal QQ.zero
      let scalar_mul = QQ.mul
    end)
  (* Simplex tableau *)
  type t =
    { tbl_generators : V.t array (* All cone generators *)
    ; tbl_index : int array      (* Indices into generator array, forming a
                                    basis for its span *)
    ; mutable tbl_map : Map.t (* Linear map sending tbl_index(i) to the unit
                                 vector in direction i.  Applying tbl_map
                                 expresses a vector as a linear combination of
                                 the tbl_index basis *)
    }

  (* Replace ith element of the basis with jth generator *)
  let _pivot tableau i j =
    (* Express jth generator as a linear combination of the elements of the
       basis *)
    let v = BatOption.get (Map.apply tableau.tbl_map tableau.tbl_generators.(j)) in
    (* Express ith generator as a linear combination of the elements of basis
       obtained by swapping the ith element of the basis with the jth
       generator *)
    let u =
      let (a, v') = QQV.pivot i v in
      QQV.add_term (QQ.of_int (-1)) i v'
      |> QQV.scalar_mul (QQ.negate (QQ.inverse a))
    in
    let map =
      Map.compose tableau.tbl_map (fun x ->
          let (a, x') = QQV.pivot i x in
          QQV.add x' (QQV.scalar_mul a u))
    in
    tableau.tbl_index.(i) <- j;
    tableau.tbl_map <- map

  let _solve_primal tableau target = Map.apply tableau.tbl_map target

  (* Find a functional that vanishes on all basis vectors except for i, where
     it evaluates to 1. *)
  let _solve_dual tableau i =
    let f =
      BatEnum.fold (fun f (src, tgt) ->
          Fun.add_exn src (QQ.negate (QQV.coeff i tgt)) f)
        Fun.empty
        (Map.enum tableau.tbl_map)
    in
    fun v -> BatOption.get (Fun.apply f v)

  let make generators =
    (* Find a subset of generators that forms a basis for the linear space
       spanned by generators *)
    let dim = ref 0 in
    let (index,map) =
      BatArray.fold_lefti (fun (index,map) i gen ->
          let target = QQV.of_term QQ.one (!dim) in
          match Map.add gen target map with
          | Some map' ->
            incr dim;
            (i::index, map')
          | None -> (index, map))
        ([], Map.empty)
        generators
    in
    { tbl_generators = generators
    ; tbl_index = Array.of_list (List.rev index)
    ; tbl_map = map }

  let solve tableau target =
    let rec go () =
      match _solve_primal tableau target with
      | None ->
        (* Target vector is not in the span of the cone *)
        None
      | Some result ->
        (* If result is non-negative then we're done.  Otherwise, find
           the smallest index h such that result(h) < 0 *)
        let r =
          QQV.fold (fun i c r ->
              if QQ.lt c QQ.zero then
                match r with
                | Some j ->
                  if tableau.tbl_index.(i) < tableau.tbl_index.(j) then
                    Some i
                  else
                    Some j
                | None -> Some i
              else r)
            result
            None
        in
        match r with
        | None ->
          (* Coefficients in result are all non-negative *)
          let r =
            QQV.fold
              (fun dim a vec -> QQV.add_term a tableau.tbl_index.(dim) vec)
              result
              QQV.zero
          in
          Some r
        | Some h ->
          (* Find a linear functional c such that { x : c(x) = 0 } is
             the span of the tableau minus h, and c(b_h) = 1. *)
          let c = _solve_dual tableau h in
          (* Find smallest s such that cs < 0 *)
          (try
             let s =
               BatArray.findi
                 (fun v -> QQ.lt (c v) QQ.zero)
                 tableau.tbl_generators
             in
             _pivot tableau h s;
             go ()
           with Not_found -> None)
    in
    go ()

  let make generators  = Log.time "Simplex" make generators
  let solve tableau target = Log.time "Simplex" (solve tableau) target
end
    

module Solver = struct
  include MakeSolver(SrkUtil.Int)(V)
end



(* A cone C is represented by a set of lines L and a set of rays R,
   with C = span(L) + cone(R), and each ray reduced w.r.t. L.  In a
   *normal* cone, cone(R) is salient.  In a *minimal* cone, cone(R) is
   salient and for any proper subset R' of R, cone(R) != cone(R'). *)
type t = 
  { mutable lines : QS.t
  ; mutable rays : V.t list
  ; mutable normal : bool
  ; mutable minimal : bool
  ; dim : int }

let simplex generators target =
  Solver.solve (Solver.make generators) target

let normalize cone =
  if not cone.normal then
    (* cone(R) has an additive unit iff cone([r | 1] : r in R)
       contains [0 | 1].  *)
    let dim = cone.dim  in
    let rays' = List.map (V.add_term QQ.one dim) cone.rays |> Array.of_list in
    let project = V.add_term (QQ.of_int (-1)) dim in (* map [r|1] -> r *)
    let target = (V.of_term QQ.one dim) in
    let rec go lin rays' =
      match simplex rays' target with
      | None -> (lin, rays')
      | Some result ->
        (* Writing result as [a1 ... an] and rays' as [ [r1 | 1]
           ... [rn | 1 ] ], we have a1r1 + ... + anrn = 0, and not
           all a1 ... an are zero.  Each ray ri with non-zero
           coefficient ai belongs to the lineality space. *)
        let lin =
          V.fold
            (fun i _ lin -> QS.add (project rays'.(i)) lin)
            result
            lin
        in
        let rays' =
          BatArray.filter_map (fun v ->
              let v' = QS.reduce lin v in
              if V.is_zero (project v') then None
              else Some v')
            rays'
        in
        go lin rays'
    in
    let (lines, rays) = go cone.lines rays' in
    cone.lines <- lines;
    cone.rays <- List.map (QS.reduce lines % project) (Array.to_list rays);
    cone.normal <- true

let lineality cone =
  normalize cone;
  BatList.of_enum (QS.basis cone.lines)
    
let make ~lines ~rays dim =
  let basis = BatList.fold_left (fun vs v -> QS.add v vs) QS.zero lines in
  { lines = basis;
    rays = List.map (QS.reduce basis) rays;
    normal = false;
    minimal = false;
    dim = dim }

let mem v cone =
  match simplex (Array.of_list cone.rays) (QS.reduce cone.lines v) with
  | Some _ -> true
  | None -> false

let minimize cone =
  if not cone.minimal then
    begin
      normalize cone;
      let rec go left right =
        match right with
        | [] -> left
        | x::xs ->
           if mem x { cone with rays = List.rev_append left xs } then
             go left xs
           else
             go (x::left) right
      in
      cone.rays <- go [] cone.rays;
      cone.minimal <- true
    end

let lines cone = BatList.of_enum (QS.basis cone.lines)
let rays cone = cone.rays
let generators cone =
  List.fold_left (fun generators v -> v::(V.negate v)::generators) cone.rays (lines cone)

let join c d =
  if c.dim != d.dim then
    invalid_arg "Cone.join: incompatible dimensions"
  else
    let lines = QS.sum c.lines d.lines in
    let rays = List.map (QS.reduce lines) (List.rev_append c.rays d.rays) in
    { dim = c.dim;
      lines = lines;
      rays = rays;
      normal = false;
      minimal = false }

let apron0_of cone =
  let e = BatList.enum [(`Vertex, V.zero)] in
  List.iter (fun v -> BatEnum.push e (`Ray, v)) cone.rays;
  BatEnum.iter (fun v -> BatEnum.push e (`Line, v)) (QS.basis cone.lines);
  DD.of_generators cone.dim e

let dual cone =
  let lines, rays =
    BatEnum.fold
      (fun (lines, rays) (kind, v) ->
         match kind with
         | `Zero -> (QS.add v lines, rays)
         | `Nonneg -> (lines, v::rays)
         | `Pos -> assert false)
      (QS.zero, [])
      (DD.enum_constraints (apron0_of cone))
  in
  { dim = cone.dim
  ; lines = lines
  ; rays = List.map (QS.reduce lines) rays
  ; normal = true
  ; minimal = true }


let meet c d =
  if c.dim != d.dim then
    invalid_arg "Cone.meet: incompatible dimensions"
  else
    let dim = c.dim in
    let c = apron0_of c in
    let d = apron0_of d in
    let lines, rays =
      BatEnum.fold
        (fun (lines, rays) (kind, v) ->
           match kind with
           | `Line -> (QS.add v lines, rays)
           | `Ray -> (lines, v::rays)
           | `Vertex ->
             assert (V.is_zero v);
             (lines, rays))
        (QS.zero, [])
        (DD.enum_generators (DD.meet c d))
    in
    let rays = List.map (QS.reduce lines) rays in
    { dim = dim;
      lines = lines;
      rays = rays;
      normal = true;
      minimal = true }

let image m cone =
  let dim = M.nb_rows m in
  let f = M.vector_right_mul m in
  make ~lines:(List.map f (lines cone)) ~rays:(List.map f (lines cone)) dim

let leq c d =
  List.for_all (fun v -> mem v d) (generators c)

let equal c d = leq c d && leq d c

let dim cone = cone.dim

let pp formatter cone =
  let pp_sep formatter () = Format.fprintf formatter "@;" in
  Format.fprintf formatter "Lines: @[<v 0>%a@]@\nRays:  @[<v 0>%a@]"
    (SrkUtil.pp_print_enum_nobox ~pp_sep V.pp) (BatList.enum (lines cone))
    (SrkUtil.pp_print_enum_nobox ~pp_sep V.pp) (BatList.enum (rays cone))

module NormalizCone = struct

  module D = Linear.MakeDenseConversion(SrkUtil.Int)(V)

  (* Rescale vector such that the selected coefficients are integral and
     relatively prime *)
  let normalize v =
    Linear.QQVector.scalar_mul (QQ.inverse (Linear.QQVector.gcd_entries v)) v

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

  let hilbert_basis cone =
    let open Normalizffi in
    let lineality = List.map normalize (lines cone) in
    let rays = List.map normalize cone.rays in
    let ctx = D.min_context (BatList.enum (lineality @ rays)) in
    let normaliz_rays =
      BatList.concat_map (fun line -> [line ; V.negate line]) lineality
      |> BatList.append cone.rays
      |> BatList.map (densify ctx) in
    let cone = Normaliz.empty_cone
               |> Normaliz.add_rays normaliz_rays |> Result.get_ok
               |> Normaliz.new_cone in
    let pp_list_list fmt =
      Format.fprintf fmt "@[<v 0>%a@]"
        (Format.pp_print_list
           (Format.pp_print_list
              ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
              (fun fmt x -> Format.fprintf fmt "%s" (Mpzf.to_string x)))
        ) in
    logf ~level:`trace "Computing Hilbert basis for rays:@; @[%a@]@;"
      pp_list_list normaliz_rays;
    let (pointed_hilbert_basis, lineality_basis) =
      (Normaliz.hilbert_basis cone,  Normaliz.get_lineality_space cone)
      |> (fun (l1, l2) ->
        let sparsify = List.map (sparsify ctx) in
        (sparsify l1, sparsify l2))
    in
    logf ~level:`trace "pointed HB: @[<v 0>%a@]@; linear HB: @[<v 0>%a@]@;
                        pointed HB has %d vectors, linear HB has %d vectors@]"
      (Format.pp_print_list ~pp_sep:Format.pp_print_cut
         Linear.QQVector.pp)
      pointed_hilbert_basis
      (Format.pp_print_list ~pp_sep:Format.pp_print_cut
         Linear.QQVector.pp)
      lineality_basis
      (List.length pointed_hilbert_basis) (List.length lineality_basis);
    pointed_hilbert_basis
    @ lineality_basis
    @ List.map Linear.QQVector.negate lineality_basis

end

let hilbert_basis = NormalizCone.hilbert_basis
