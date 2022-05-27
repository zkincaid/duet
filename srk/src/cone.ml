open BatPervasives

module V = Linear.QQVector
module M = Linear.QQMatrix
module VS = Linear.QQVectorSpace
module IntSet = SrkUtil.Int.Set
module IntMap = SrkUtil.Int.Map

(* QS represents a vector space L along with a function reduce that
   maps each vector in QQ^omega to its representative in the quotient
   QQ^omega/L.  Representatives are chosen to use as few dimensions as
   possible. *)
module QS = Linear.MakeLinearSpace(QQ)(SrkUtil.Int)(Linear.QQVector)

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

type tableau =
  { tbl_generators : V.t array (* All cone generators *)
  ; tbl_index : int array      (* Indices into generator array, forming a basis for its span *)
  ; mutable tbl_basis : M.t }  (* Matrix where ith row is tbl_generators(tbl_index.(i)) *)
  

(* Replace ith index with j in a simplex tableau *)
let _pivot tableau i j =
  let basis =
    snd (M.pivot i tableau.tbl_basis)
    |> M.add_row i tableau.tbl_generators.(j)
  in
  tableau.tbl_index.(i) <- j;
  tableau.tbl_basis <- basis

let _solve_primal tableau target =
  Linear.solve (M.transpose tableau.tbl_basis) target

let _solve_dual tableau target =
  (Linear.solve tableau.tbl_basis) target

let simplex generators target =
  (* Find a subset of generators that forms a basis for the linear space
     spanned by generators *)
  let (index,vs,_) =
    Log.time "init"
      (BatArray.fold_lefti (fun (index,vs,qs) i gen ->
           if QS.mem qs gen then
             (index, vs, qs)
           else
             (i::index, gen::vs, QS.add gen qs))
      ([], [], QS.zero))
      generators
  in
  let tableau =
    { tbl_generators = generators;
      tbl_index = Array.of_list (List.rev index);
      tbl_basis = M.of_rows (List.rev vs) }
  in
  let rec go () =
    match _solve_primal tableau target with
    | None ->
       (* Target vector is not in the span of the cone *)
       None
    | Some result ->
       (* If result is non-negative then we're done.  Otherwise, find
          the smallest index h such that result(h) < 0 *)

      let r =
        V.fold (fun i c r ->
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
           V.fold
             (fun dim a vec -> V.add_term a tableau.tbl_index.(dim) vec)
             result
             V.zero
          in
          Some r
       | Some h ->
          (* Find a linear functional c such that { x : c(x) = 0 } is
             the span of the tableau minus h, and c(b_h) = 1. *)
          let c =
            BatOption.get (_solve_dual tableau (V.of_term QQ.one h))
          in
          (* Find smallest s such that cs < 0 *)
          (try
             let s =
               BatArray.findi
                 (fun v -> QQ.lt (V.dot c v) QQ.zero)
                 tableau.tbl_generators
             in
             _pivot tableau h s;
             go ()
           with Not_found -> None)
  in
  go ()

let simplex generators target =
  Log.time "Simplex" (simplex generators) target

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

let lexpr_of_vec vec =
  let mk (coeff, dim) = (SrkApron.coeff_of_qq coeff, dim) in
  Apron.Linexpr0.of_list
    None
    (BatList.of_enum (BatEnum.map mk (V.enum vec)))
    None
  

let vec_of_lexpr linexpr =
  let open Apron in
  let vec = ref V.zero in
  Linexpr0.iter (fun coeff dim ->
      match SrkApron.qq_of_coeff coeff with
      | Some qq -> vec := V.add_term qq dim (!vec)
      | None -> assert false)
    linexpr;
  !vec

let apron0_of cone =
  let open Apron in
  let man = Polka.manager_alloc_loose () in
  let generators =
    BatEnum.fold
      (fun generators v ->
        Generator0.(make (lexpr_of_vec v) LINE)::generators)
      (List.map (fun v -> Generator0.(make (lexpr_of_vec v) RAY)) cone.rays)
      (QS.basis cone.lines)
  in
  let zero = (* Singleton set {0} *)
    let one = Coeff.s_of_int 1 in
    let unit i = Linexpr0.of_list None [one, i] None in
    Abstract0.of_lincons_array man 0 cone.dim
      (Array.init cone.dim (fun i -> Lincons0.(make (unit i) EQ)))
  in
  Abstract0.add_ray_array man zero (BatArray.of_list generators)

let dual cone =
  let open Apron in
  let ap = apron0_of cone in
  let man = Abstract0.manager ap in
  let (lines, rays) =
    BatArray.fold_left
      (fun (lines, rays) lincons ->
        Lincons0.(let vec = vec_of_lexpr lincons.linexpr0 in
                  match lincons.typ with
                  | EQ -> (QS.add vec lines, rays)
                  | SUPEQ -> (lines, vec::rays)
                  | _ -> assert false))
      (QS.zero, [])
      (Abstract0.to_lincons_array man ap)
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
    let open Apron in
    let dim = c.dim in
    let c = apron0_of c in
    let d = apron0_of d in
    let man = Abstract0.manager c in
    let (lines, rays) =
      BatArray.fold_left
        (fun (lines, rays) generator ->
          Generator0.(let vec = vec_of_lexpr generator.linexpr0 in
                      match generator.typ with
                      | LINE -> (QS.add vec lines, rays)
                      | RAY -> (lines, vec::rays)
                      | VERTEX ->
                         assert (V.is_zero vec);
                         (lines, rays)
                      | _ -> assert false))
        (QS.zero, [])
        (Abstract0.to_generator_array man (Abstract0.meet man c d))
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
