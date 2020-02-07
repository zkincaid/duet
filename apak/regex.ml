open Srk

type 'a regex =
  | Alpha of 'a
  | Cat of (('a regex) * ('a regex))
  | Union of (('a regex) * ('a regex))
  | Star of ('a regex)
  | Empty
  | Epsilon

(** Open type for folding *)
type ('a, 'b) open_regex =
  | OAlpha of 'a
  | OCat of ('b * 'b)
  | OUnion of ('b * 'b)
  | OStar of ('b)
  | OEmpty
  | OEpsilon

let rec fold_regex f = function
  | Alpha a -> f (OAlpha a)
  | Cat (a,b) -> f (OCat (fold_regex f a, fold_regex f b))
  | Union (a,b) -> f (OUnion (fold_regex f a, fold_regex f b))
  | Star a -> f (OStar (fold_regex f a))
  | Empty -> f OEmpty
  | Epsilon -> f OEpsilon

let rec regex_compare alpha_compare x y =
  let go  = regex_compare alpha_compare in
  match x,y with
  | (Alpha a, Alpha b) -> alpha_compare a b
  | (Star a, Star b) -> go a b
  | (Cat (a0,b0), Cat (a1,b1)) | (Union (a0,b0), Union (a1,b1)) -> begin
      match go a0 a1 with
      | 0 -> go b0 b1
      | other -> other
    end
  | (Empty, Empty) | (Epsilon, Epsilon) -> 0
  | (Alpha _, _) -> 1
  | (_, Alpha _) -> -1
  | (Star _, _) -> 1
  | (_, Star _) -> -1
  | (Cat _, _) -> 1
  | (_, Cat _) -> -1
  | (Union _, _) -> 1
  | (_, Union _) -> -1
  | (Empty, _) -> 1
  | (_, Empty) -> -1

(** Calculate the length of the shortest word accepted by a regular
    expression *)
let min_length =
  let f = function
    | OEmpty -> None
    | OEpsilon -> Some 0
    | OAlpha _ -> Some 1
    | OCat (Some x, Some y) -> Some (x + y)
    | OCat _ -> None
    | OUnion (Some x, Some y) -> Some (min x y)
    | OUnion (None, x) -> x
    | OUnion (x, None) -> x
    | OStar _ -> Some 0
  in
  fun x -> fold_regex f x

(** {1 Kleene algebra operations}

    These operations apply some simplifications as well, so they should be
    used in preference to the regex constructors. *)

(** Kleene closure *)
let regex_star = function
  | Epsilon -> Epsilon
  | Empty   -> Epsilon
  | x       -> Star x

(** Catenation *)
let regex_mul x y = match x, y with
  | (x, Epsilon) | (Epsilon, x) -> x
  | (Empty, _) | (_, Empty)     -> Empty
  | (x, y)                      -> Cat (x,y)

(** Union *)
let regex_add x y = match x, y with
  | (Empty, x) | (x, Empty)     -> x
  | (x, y)                      -> if x = y then x else Union (x,y)

let rec pp_regex pp_alpha formatter = function
  | Alpha x -> pp_alpha formatter x
  | Cat (x, y) ->
    Format.fprintf formatter "(%a@,%a)"
      (pp_regex pp_alpha) x
      (pp_regex pp_alpha) y
  | Union (x, y) ->
    Format.fprintf formatter "(%a@,+%a)"
      (pp_regex pp_alpha) x
      (pp_regex pp_alpha) y
  | Star x ->
    Format.fprintf formatter "@[(%a)*@]"
      (pp_regex pp_alpha) x
  | Empty -> Format.pp_print_string formatter "{}"
  | Epsilon -> Format.pp_print_string formatter "@"

(** Make an initial Kleene algebra (regular expressions over the alphabet
    [M.t]).  The operations are the same as their polymorphic variants
    ([regex_star], [regex_mul], [regex_add]), but specialized to [M.t] *)
module MakeKA (M : Putil.S) =
struct
  type t = M.t regex [@@deriving show]

  let star = regex_star
  let mul = regex_mul
  let add = regex_add
  let zero = Empty
  let one = Epsilon
end

(** Normalized regular expressions attempt to make more ambitious
    simplifications than those implemented by {!regex_star}, {!regex_add}, and
    {!regex_mul}.  Note, however, that normalized regexes are {b not}
    canonical.

    This functor also implements a fast emptiness-of-intersection algorithm
    (but there is no real reason this algorithm should be tied to normalized
    regular expressions *)
module NormalizedRegex (M : sig
    include Putil.Ordered
    val consistent : t -> t -> bool
  end) =
struct
  module rec N : sig
    type t =
      | NCat of (t list)
      | NUnion of NSet.t
      | NStar of t
      | NAlpha of M.t
      | NComplement of t
    val show : t -> string
    include Putil.Ordered with type t := t
  end = struct
    type t =
      | NCat of (t list)
      | NUnion of NSet.t
      | NStar of t
      | NAlpha of M.t
      | NComplement of t
            [@@deriving ord]

    let rec pp formatter = function
      | NAlpha a -> M.pp formatter a
      | NStar (NAlpha a) ->
        M.pp formatter a;
        Format.pp_print_string formatter "*"
      | NStar x ->
        Format.fprintf formatter "@[(%a)*@]" pp x
      | NCat [] -> Format.pp_print_string formatter "@"
      | NCat xs ->
        let pp_elt formatter x = match x with
          | NUnion _ ->
            Format.fprintf formatter "@[(%a)@]" pp x
          | _ -> pp formatter x
        in
        SrkUtil.pp_print_enum
          ~pp_sep:(fun _ () -> ())
          pp_elt
          formatter
          (BatList.enum xs)
      | NUnion xs ->
        if NSet.is_empty xs then Format.pp_print_string formatter "{}"
        else
          SrkUtil.pp_print_enum
            ~pp_sep:(fun formatter () -> Format.fprintf formatter "@,+" )
            pp
            formatter
            (NSet.enum xs)
      | NComplement x ->
        Format.fprintf formatter "@[~(%a)@]" pp x
    let show = SrkUtil.mk_show pp
  end
  and NSet : Putil.Set.S with type elt = N.t = Putil.Set.Make(N)

  include N

  let equal x y = compare x y = 0

  let to_cat = function
    | NCat a -> a
    | x      -> [x]
  let to_union = function
    | NUnion a -> a
    | x        -> NSet.singleton x

  let zero = NUnion NSet.empty (* empty *)
  let one = NCat [] (* epsilon *)
  let alpha a = NAlpha a

  let ncat xs =
    if List.mem zero xs then zero
    else match xs with
      | [x] -> x
      | xs  -> NCat xs

  let nunion x =
    let x = if NSet.mem zero x then NSet.remove zero x else x in
    if NSet.cardinal x = 1 then NSet.choose x else NUnion x

  let star x = match x with
    | NStar _ -> x
    | NCat [] -> one
    | NUnion ys ->
      let ys = if NSet.mem one ys then NSet.remove one ys else ys in
      if NSet.is_empty ys then one else NStar (nunion ys)
    | _      -> NStar x
  let mul a b = ncat ((to_cat a)@(to_cat b))
  let add a b = nunion (NSet.union (to_union a) (to_union b))

  let normalize =
    let f = function
      | OAlpha a -> NAlpha a
      | OCat (a, b) -> mul a b
      | OUnion (a, b) -> add a b
      | OStar a -> star a
      | OEmpty -> zero
      | OEpsilon -> one
    in
    fold_regex f

  let rec unnormalize = function
    | NCat xs ->
      List.fold_right (fun x y -> regex_mul (unnormalize x) y) xs Epsilon
    | NUnion xs ->
      NSet.fold (fun x y -> regex_add (unnormalize x) y) xs Empty
    | NStar x -> Star (unnormalize x)
    | NAlpha a -> Alpha a
    | NComplement _ -> failwith "Cannot unnormalize a complement"

  let rec accepts_epsilon = function
    | NCat xs -> List.for_all accepts_epsilon xs
    | NUnion xs -> NSet.exists accepts_epsilon xs
    | NStar _ -> true
    | NAlpha _ -> false
    | NComplement x -> not (accepts_epsilon x)

  let rec derivative a = function
    | NCat xs ->
      let rec go = function
        | (y::ys) ->
          let dy = derivative a y in
          let dy_ys = mul dy (NCat ys) in
          if accepts_epsilon y then add dy_ys (go ys) else dy_ys
        | [] -> zero
      in
      go xs
    | NUnion xs ->
      NSet.fold (fun x -> add (derivative a x)) xs zero
    | NStar x -> mul (derivative a x) (star x)
    | NAlpha b -> if M.consistent a b then one else zero
    | NComplement x -> NComplement (derivative a x)

  module ASet = Set.Make(M)

  let rec next_letters = function
    | NCat xs ->
      let rec go = function
        | (y::ys) -> let y_letters = next_letters y in
          if accepts_epsilon y then ASet.union y_letters (go ys)
          else y_letters
        | [] -> ASet.empty
      in
      go xs
    | NUnion xs ->
      NSet.fold (fun x -> ASet.union (next_letters x)) xs ASet.empty
    | NStar x -> next_letters x
    | NAlpha a -> ASet.singleton a
    | NComplement _ -> failwith "next_letters on complemented regex"

  module StateSet = Set.Make(
    struct
      type t = N.t * N.t [@@deriving ord]
    end)

  (* state pairs along with heuristic distance estimates *)
  module HStateSet = Set.Make(
    struct
      type t = int * int * N.t * N.t
      let compare (w0, x0, y0, z0) (w1, x1, y1, z1) =
        match Stdlib.compare (w0+x0) (w1+x1) with
        | 0 ->
          begin match N.compare y0 y1 with
            | 0 -> N.compare z0 z1
            | other -> other
          end
        | other -> other
    end)

  let rec min_length =
    let opt_product f x y = match x,y with
      | (Some x, Some y) -> Some (f x y)
      | _ -> None
    in
    let opt_choice f x y = match x,y with
      | (Some x, Some y) -> Some (f x y)
      | (None, y) -> y
      | (x, None) -> x
    in
    function
    | NCat xs   ->
      let f a x = opt_product (+) a (min_length x) in
      List.fold_left f (Some 0) xs
    | NUnion xs ->
      let f x a = opt_choice min a (min_length x) in
      NSet.fold f xs None
    | NAlpha _  -> Some 1
    | NStar _   -> Some 0
    | NComplement x -> if accepts_epsilon x then Some 1 else Some 0

  let intersects x y =
    let distance dx dy = match min_length dx, min_length dy with
      | (Some x, Some y) -> Some (max x y)
      | _                -> None
    in

    (* implementation of A* search *)
    let rec go open_set closed_set =
      if HStateSet.is_empty open_set then false else begin
        let (g, h, x, y) = HStateSet.min_elt open_set in
        if (accepts_epsilon x) && (accepts_epsilon y) then true else begin
          let open_set = HStateSet.remove (g, h, x, y) open_set in
          let closed_set = StateSet.add (x, y) closed_set in
          let f a open_set =
            let dx = derivative a x in
            let dy = derivative a y in
            if StateSet.mem (dx, dy) closed_set then open_set
            else (match distance dx dy with
                | Some h -> HStateSet.add (g+1, h, dx, dy) open_set
                | None   -> open_set)
          in
          let open_set = ASet.fold f (next_letters x) open_set in
          go open_set closed_set
        end
      end
    in
    match distance x y with
    | Some d -> go (HStateSet.singleton (0, d, x, y)) StateSet.empty
    | None   -> false

  let sub x y = not (intersects x (NComplement y))
  let eqv x y = (sub x y) && (sub y x)
end
