(*pp camlp4find deriving.syntax *)

open Apak

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
  let hash x = Hashtbl.hash (Mpqf.to_string x)
  let leq x y = compare x y <= 0
  let lt x y = compare x y < 0
  let geq x y = compare x y >= 0
  let gt x y = compare x y > 0
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
  let hash x = Hashtbl.hash (Mpzf.to_string x)
  let leq x y = compare x y <= 0
  let lt x y = compare x y < 0
end

type typ = TyInt | TyReal
    deriving (Compare)

type ('a,'b) open_term =
| OVar of 'b
| OConst of QQ.t
| OAdd of 'a * 'a
| OMul of 'a * 'a
| ODiv of 'a * 'a
| OFloor of 'a

type ('a,'b) term_algebra = ('a,'b) open_term -> 'a

type 'a atom =
| LeqZ of 'a
| LtZ of 'a
| EqZ of 'a

type ('a,'b) open_formula =
| OOr of 'a * 'a
| OAnd of 'a * 'a
| OAtom of 'b

type ('a,'b) formula_algebra = ('a,'b) open_formula -> 'a

type pred = Pgt | Pgeq | Plt | Pleq | Peq

let join_typ a b = match a,b with
  | TyInt, TyInt -> TyInt
  | _, _         -> TyReal

module type Var = sig
  include Putil.Ordered
  val typ : t -> typ
end

type 'a affine =
| AVar of 'a
| AConst
