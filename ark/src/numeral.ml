(*pp camlp4find deriving.syntax *)

open Apak
open Apron

module Ring = struct
  module type S = sig
    include Sig.Semiring.S
    val negate : t -> t (* additive inverse *)
    val sub : t -> t -> t
  end
  module Ordered = struct
    module type S = sig
      include S
      include Putil.OrderedMix with type t := t
    end
  end
  module Hashed = struct
    module type S = sig
      include S
      val hash : t -> int
    end
  end
end

module Field = struct
  module type S = sig
    include Ring.S
    val inverse : t -> t (* multiplicative inverse *)
    val div : t -> t -> t
  end
  module Ordered = struct
    module type S = sig
      include S
      include Putil.OrderedMix with type t := t
    end
  end
end

(*
type qq = Num.num (* Rationals *)
type zz = Big_int.big_int (* Integers  *)

(* Field of rationals *)
module QQ = struct
  type t = qq
  module M = Num

  include Putil.MakeFmt(struct
    type a = t
    let format formatter x =
      Format.pp_print_string formatter (M.string_of_num x)
  end)
  module Compare_t = struct
    type a = t
    let compare = M.compare_num
  end
  let show = Show_t.show
  let format = Show_t.format
  let compare = Compare_t.compare
  let add = M.add_num
  let sub = M.sub_num
  let mul = M.mult_num
  let div = M.div_num
  let zero = M.num_of_int 0
  let one = M.num_of_int 1
  let equal x y = M.compare_num x y = 0
  let negate = M.minus_num
  let inverse x = M.div_num one x

  let of_int = M.num_of_int
  let of_zz = M.num_of_big_int
  let of_frac x y = M.div_num (M.num_of_int x) (M.num_of_int y)
  let of_zzfrac x y = M.div_num (M.num_of_big_int x) (M.num_of_big_int y)

  let of_string = M.num_of_string
  let to_zzfrac x = match x with
    | M.Int x -> (Big_int.big_int_of_int x, Big_int.big_int_of_int 1)
    | M.Big_int x -> (x, Big_int.big_int_of_int 1)
    | M.Ratio r -> (Ratio.numerator_ratio r, Ratio.denominator_ratio r)

  (* unsafe *)
(*
  let to_frac qq =
    let (num,den) = to_zzfrac qq in
    (Mpz.get_int num, Mpz.get_int den)
*)
  let numerator x = match x with
    | M.Int x -> Big_int.big_int_of_int x
    | M.Big_int x -> x
    | M.Ratio r -> Ratio.numerator_ratio r
  let denominator x = match x with
    | M.Int x -> Big_int.big_int_of_int 1
    | M.Big_int x -> Big_int.big_int_of_int 1
    | M.Ratio r -> Ratio.denominator_ratio r
  let hash (x : t) = Hashtbl.hash x
end

(* Ring of integers *)
module ZZ = struct
  type t = zz
  open Big_int

  include Putil.MakeFmt(struct
    type a = t
    let format formatter x =
      Format.pp_print_string formatter (string_of_big_int x)
  end)
  module Compare_t = struct
    type a = t
    let compare = compare_big_int
  end
  let show = Show_t.show
  let format = Show_t.format
  let compare = Compare_t.compare
  let add = add_big_int
  let sub = sub_big_int
  let mul = mult_big_int
  let negate = minus_big_int
  let floor_div = div_big_int
  let gcd = gcd_big_int

  let of_int = big_int_of_int
  let of_string = big_int_of_string
  let one = of_int 1
  let zero = of_int 0
  let equal x y = compare x y = 0
  let to_int x =
    if is_int_big_int x then Some (int_of_big_int x) else None
  let hash (x : t) = Hashtbl.hash x
  let leq x y = compare x y <= 0
  let lt x y = compare x y < 0
end
*)


type qq = Mpqf.t (* Rationals *)
type zz = Mpzf.t (* Integers  *)

(* Field of rationals *)
module QQ = struct
  type t = Mpqf.t

  include Putil.MakeFmt(struct
    type a = t
    let format = Mpqf.print
  end)
  module Compare_t = struct
    type a = t
    let compare = Mpqf.cmp
  end
  let show = Show_t.show
  let format = Show_t.format
  let compare = Compare_t.compare
  let add = Mpqf.add
  let sub = Mpqf.sub
  let mul = Mpqf.mul
  let div = Mpqf.div
  let zero = Mpqf.of_int 0
  let one = Mpqf.of_int 1
  let equal = Mpqf.equal
  let negate = Mpqf.neg
  let inverse = Mpqf.inv

  let of_int = Mpqf.of_int
  let of_zz = Mpqf.of_mpz
  let of_frac = Mpqf.of_frac
  let of_zzfrac = Mpqf.of_mpz2
  let of_float = Mpqf.of_float
  let of_string = Mpqf.of_string
  let to_zzfrac = Mpqf.to_mpzf2
  (* unsafe *)
  let to_frac qq =
    let (num,den) = to_zzfrac qq in
    (Mpz.get_int num, Mpz.get_int den)
  let to_zz qq =
    let (num, den) = to_zzfrac qq in
    if Mpz.cmp den (Mpzf.of_int 1) == 0 then Some num
    else None

  let numerator = Mpqf.get_num
  let denominator = Mpqf.get_den
  let hash (x : t) = Hashtbl.hash x
  let leq x y = compare x y <= 0
  let lt x y = compare x y < 0
  let exp x k =
    let rec go x k =
      if k = 0 then zero
      else if k = 1 then x
      else begin
	let y = go x (k / 2) in
	let y2 = mul y y in
	if k mod 2 = 0 then y2 else mul x y2
      end
    in
    if k < 0 then Mpqf.inv (go x (-k))
    else go x k
  let floor x =
    let (num, den) = to_zzfrac x in
    Mpzf.fdiv_q num den
end

(* Ring of integers *)
module ZZ = struct
  type t = Mpzf.t

  include Putil.MakeFmt(struct
    type a = t
    let format = Mpzf.print
  end)
  module Compare_t = struct
    type a = t
    let compare = Mpzf.cmp
  end
  let show = Show_t.show
  let format = Show_t.format
  let compare = Compare_t.compare
  let add = Mpzf.add
  let sub = Mpzf.sub
  let mul = Mpzf.mul
  let negate = Mpzf.neg
  let floor_div = Mpzf.fdiv_q
  let gcd = Mpzf.gcd
  let lcm = Mpzf.lcm

  let of_int = Mpzf.of_int
  let of_string = Mpzf.of_string
  let one = of_int 1
  let zero = of_int 0
  let equal x y = compare x y = 0
  let to_int x =
    if Mpz.fits_int_p x then Some (Mpz.get_int x) else None
  let hash (x : t) = Hashtbl.hash x
  let leq x y = compare x y <= 0
  let lt x y = compare x y < 0
end
