open Normalizffi
open BatPervasives

module QQEndo = Linear.MakeLinearMap(QQ)(Int)(Linear.QQVector)(Linear.QQVector)

module D = Linear.MakeDenseConversion(SrkUtil.Int)(Linear.QQVector)

module V = Linear.QQVector

include Log.Make(struct let name = "srk.intLattice" end)

let () = my_verbosity_level := `info

let little_endian_list_of_vector num_dims v =
  let arr = Array.make num_dims QQ.zero in
  BatEnum.iter
    (fun dim -> arr.(dim) <- V.coeff dim v)
    (0 --^ num_dims);
  Array.to_list arr

let vector_of_list l =
  List.fold_left (fun (v, idx) elt -> (V.add_term elt idx v, idx + 1)) (V.zero, 0) l
  |> fst

module L : sig

  type hnf
  type unreduced

  type 'form t

  val bottom: unreduced t

  val of_generators: V.t list -> unreduced t

  val hermitize: ?compare:(int -> int -> int) -> 'form t -> hnf t

  val forget: hnf t -> unreduced t

  val generators: 'form t -> V.t list

  val member: V.t -> hnf t -> bool

  val max_dim: 'form t -> V.dim option

  val project: keep:(int -> bool) -> 'form t -> unreduced t

  val project_as_dual: keep:(int -> bool) -> 'form t -> hnf t

  val sum: 'form t -> 'form t -> unreduced t

  val subset: 'form t -> hnf t -> bool

  val equal: hnf t -> hnf t -> bool

  val intersect: 'form t -> 'form t -> hnf t

  val pp: (Format.formatter -> int -> unit) -> Format.formatter -> 'form t -> unit

end = struct

  module Vs = BatSet.Make (V)
  module Endo = Linear.MakeLinearMap(QQ)(Int)(Linear.QQVector)(Linear.QQVector)

  type hnf = { inverse: Endo.t option ref }
  type unreduced = unit

  module IntSet = SrkUtil.Int.Set
  module IntMap = SrkUtil.Int.Map

  (** A lattice is represented as a matrix 1/[denominator] G, where each vector
      in G is viewed as a row of a matrix. If the lattice is in HNF, it means
      that this matrix is in row-Hermite normal form.

      If G is empty, the lattice is the zero lattice, not the empty lattice;
      lattices must contain 0.
   *)

  type 'form t =
    {
      denominator: ZZ.t
    ; generators: Vs.t
    ; aux: 'form
    }

  type conversion =
    {
      to_rank: int IntMap.t (* according to an order *)
    ; from_rank: int IntMap.t
    ; num_dims: int
    }

  let of_generators vectors : unreduced t =
    let denominator = List.fold_left
                        (fun m v -> ZZ.lcm m (V.common_denominator v))
                        ZZ.one
                        vectors
    in
    let scale v = V.scalar_mul (QQ.of_zz denominator) v in
    let generators =
      List.fold_left (fun set v -> Vs.add (scale v) set) Vs.empty vectors
    in
    {
      denominator
    ; generators
    ; aux = ()
    }

  let dimensions t =
    Vs.fold
      (fun v dimensions ->
        V.fold (fun dim _ dims -> IntSet.add dim dims) v dimensions
      )
      t.generators
      IntSet.empty

  (* If dim < dim' according to [compare], [dim'] is left of [dim] in row HNF. *)
  let conversion compare t =
    let rev_compare x y = -(compare x y) in
    let dims =
      BatList.sort rev_compare (IntSet.to_list (dimensions t))
    in
    let (num_dims, to_rank, from_rank) =
      BatEnum.fold
        (fun (rank, to_rank, from_rank) dim ->
          ( rank + 1
          , IntMap.add dim rank to_rank
          , IntMap.add rank dim from_rank
          )
        )
        (0, IntMap.empty, IntMap.empty)
        (BatList.enum dims)
    in
    {
      to_rank
    ; from_rank
    ; num_dims
    }

  let remap map v =
    V.fold
      (fun dim x u -> match IntMap.find_opt dim map with
                      | Some dim' -> V.add_term x dim' u
                      | None -> failwith (Format.asprintf "Dimension %d absent" dim)
      )
      v
      V.zero

  let mpz_list conversion v =
    remap conversion.to_rank v
    |> little_endian_list_of_vector conversion.num_dims
    |> List.map
         (fun q -> match QQ.to_zz q with
                   | Some z -> ZZ.mpz_of z
                   | None -> failwith "bug: vector in lattice is not integral"
         )

  let vector_of conversion mpz_list =
    List.map (QQ.of_zz % ZZ.of_mpz) mpz_list
    |> vector_of_list
    |> remap conversion.from_rank

  (*
   ZZ L = (1/d) ZZ (d L) = (1/d) ZZ B = ZZ (1/d B).
   *)
  let hermitize ?(compare=Int.compare) t =
    let conv = conversion compare t in
    let matrix = List.map (mpz_list conv) (Vs.to_list t.generators) in
    match matrix with
    | [] | [[]] ->
       { denominator = ZZ.one; generators = Vs.empty ; aux = { inverse = ref None } }
    | _ ->
       let level = `trace in
       let verbose = Log.level_leq (!my_verbosity_level) level in
       if verbose then Flint.set_debug true else ();
       (* Possible stack overflow when the matrix is too big. *)
       let mat = Flint.new_matrix matrix in
       Flint.hermitize mat;
       let rank = Flint.rank mat in
       let basis =
         Flint.denom_matrix_of_rational_matrix mat
         |> snd
         |> BatList.take rank (* The rows after rank should be all zeros *)
       in
       if verbose then Flint.set_debug false;
       let generators = List.map (vector_of conv) basis
                        |> Vs.of_list
       in
       { denominator = t.denominator
       ; generators = generators
       ; aux = { inverse = ref None }
       }

  let generators t =
    let rescale v =
      V.scalar_mul (QQ.inverse (QQ.of_zz t.denominator)) v in
    List.map rescale (Vs.to_list (t.generators))

  let inverse_of generators =
    let std_vector = Linear.QQVector.of_term QQ.one in
    let (f, _) =
      List.fold_left (fun (f, idx) g ->
          let f' = Endo.add g (std_vector idx) f in
          match f' with
          | None -> assert false
          | Some f' ->
             (f', idx + 1))
        (Endo.empty, 0) (Vs.to_list generators)
    in f

  let integral v =
    Linear.QQVector.fold
      (fun _ scalar bool ->
        bool && ZZ.equal (QQ.denominator scalar) ZZ.one)
      v true

  let member v t =
    let v = V.scalar_mul (QQ.of_zz t.denominator) v in
    let invert inverse v =
      begin match Endo.apply inverse v with
      | Some x -> integral x
      | None -> false
      end
    in
    match !(t.aux.inverse) with
    | Some inverse ->
       invert inverse v
    | None ->
       let inverse = inverse_of t.generators in
       t.aux.inverse := Some inverse;
       invert inverse v

  let max_dim t = IntSet.max_elt_opt (dimensions t)

  let project ~keep t =
    let generators' =
      Vs.map
        (fun v ->
          V.fold
            (fun dim entry u -> if keep dim then V.add_term entry dim u else u)
            V.zero
            v
        )
        t.generators
      |> Vs.to_list
    in
    of_generators generators'

  let project_as_dual ~keep t =
    let compare x y = match keep x, keep y with
      | true, false -> -1
      | false, true -> 1
      | _, _ -> Int.compare x y
    in
    hermitize ~compare t

  let pp pp_dim fmt t =
    let rescale v = V.scalar_mul (QQ.of_zzfrac ZZ.one t.denominator) v in
    let generators = Vs.map rescale t.generators |> Vs.to_list in
    match generators with
    | [] -> Format.fprintf fmt "{0}"
    | _ -> Format.fprintf fmt
             "@[<v 0>{%a}@]"
             (SrkUtil.pp_print_list (Linear.QQVector.pp_term pp_dim))
             generators

  let bottom = of_generators []

  let sum t1 t2 =
    let rescale t v = V.scalar_mul (QQ.of_zzfrac ZZ.one t.denominator) v in
    let g1 = Vs.map (rescale t1) t1.generators in
    let g2 = Vs.map (rescale t2) t2.generators in
    of_generators (Vs.to_list (Vs.union g1 g2))

  let subset t1 t2 =
    Vs.for_all (fun v -> member v t2) t1.generators

  let equal t1 t2 =
    subset t1 t2 && subset t2 t1

  let intersect t1 t2 =
    let all_dims = IntSet.union (dimensions t1) (dimensions t2)  in
    let max_dim = IntSet.max_elt all_dims in
    let shift_vector ?(transform=identity) v =
      Linear.QQVector.enum v
      |> BatEnum.fold (fun l (scalar, dim) -> (transform scalar, dim + max_dim + 1) :: l) []
      |> Linear.QQVector.of_list
    in
    let rescale t v = V.scalar_mul (QQ.of_zzfrac ZZ.one t.denominator) v in
    let one_minus_promoted_t2 =
      Vs.map
        (fun v ->
          let v' = rescale t2 v in
          shift_vector ~transform:QQ.negate v'
          |> V.add v'
        ) t2.generators
    in
    let promoted_t1 = Vs.map (shift_vector % rescale t1) t1.generators in
    let generators = Vs.union one_minus_promoted_t2 promoted_t1 in
    of_generators (Vs.to_list generators)
    |> hermitize
    |> project_as_dual ~keep:(fun dim -> dim <= max_dim)

  let forget t =
    {
      denominator = t.denominator
    ; generators = t.generators
    ; aux = ()
    }

end

type hnf = L.hnf
type unreduced = L.unreduced

type 'form t = 'form L.t

let bottom = L.bottom
let of_generators = L.of_generators
let hermitize = L.hermitize
let generators = L.generators
let forget = L.forget
let member = L.member
let max_dim = L.max_dim
let project_as_dual = L.project_as_dual
let project = L.project
let sum = L.sum
let subset = L.subset
let equal = L.equal
let intersect = L.intersect
let pp = L.pp
