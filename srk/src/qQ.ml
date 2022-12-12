type t = Q.t

let opt_default_accuracy = ref (-1)

let pp = Q.pp_print
let show = Q.to_string

let compare = Q.compare
let equal = Q.equal
let leq x y = Q.leq x y
let lt x y = Q.lt x y

let add = Q.add
let sub = Q.sub
let mul = Q.mul
let zero = Q.zero
let one = Q.one
let div = Q.div

let negate = Q.neg
let inverse = Q.inv

let of_int = Q.of_int
let of_zz = Q.of_bigint
let of_frac = Q.of_ints
let of_zzfrac = Q.make
let of_float = Q.of_float
let of_string = Q.of_string
let to_zzfrac x = (Q.num x, Q.den x)

let to_zz x =
  if Z.equal (Q.den x) Z.one then Some (Q.num x)
  else None
let to_int x = BatOption.Monad.bind (to_zz x) ZZ.to_int
let to_float = Q.to_float

(* TODO: Z_mlgmpidl provides fast conversion *)
let of_mpq x = Q.of_string (Mpqf.to_string x)
let mpq_of x = Mpqf.of_string (show x)

let numerator = Q.num
let denominator = Q.den
let hash = Hashtbl.hash

let min = Q.min
let max = Q.max
let abs = Q.abs

let exp x k =
  let open Stdlib in
  let rec go x k =
    if k = 0 then one
    else if k = 1 then x
    else begin
      let y = go x (k / 2) in
      let y2 = Q.mul y y in
      if k mod 2 = 0 then y2 else Q.mul x y2
    end
  in
  if k < 0 then inverse (go x (-k))
  else go x k

let floor x =
  let (num, den) = to_zzfrac x in
  ZZ.fdiv num den

let ceiling x =
  let (num, den) = to_zzfrac x in
  ZZ.fdiv (ZZ.sub (ZZ.add num den) ZZ.one) den

(* Truncated continued fraction *)
let rec nudge ?(accuracy=(!opt_default_accuracy)) x =
  if accuracy < 0 then
    (x, x)
  else
    let (num, den) = to_zzfrac x in
    let (q, r) = ZZ.div_rem num den in
    if accuracy = 0 then
      (of_zz q, Q.of_bigint (ZZ.add q (ZZ.of_int 1)))
    else if r = Z.zero then
      (of_zz q, Q.of_bigint q)
    else
      let (lo, hi) = nudge ~accuracy:(accuracy - 1) (of_zzfrac den r) in
      (add (Q.of_bigint q) (inverse hi),
       add (Q.of_bigint q) (inverse lo))

let rec nudge_down ?(accuracy=(!opt_default_accuracy)) x =
  if accuracy < 0 then
    x
  else
    let (num, den) = to_zzfrac x in
    let (q, r) = ZZ.div_rem num den in
    if accuracy = 0 then
      of_zz q
    else if ZZ.equal r ZZ.zero then
      of_zz q
    else
      let hi = nudge_up ~accuracy:(accuracy - 1) (of_zzfrac den r) in
      add (of_zz q) (inverse hi)
and nudge_up ?(accuracy=(!opt_default_accuracy)) x =
  if accuracy < 0 then
    x
  else
    let (num, den) = to_zzfrac x in
    let (q, r) = Z.ediv_rem num den in
    if accuracy = 0 then
      of_zz (ZZ.add q ZZ.one)
    else if ZZ.equal r ZZ.zero then
      of_zz q
    else
      let lo = nudge_down ~accuracy:(accuracy - 1) (of_zzfrac den r) in
      add (of_zz q) (inverse lo)

let idiv x y =
  if compare y zero = 0 then invalid_arg "QQ.idiv: divide by zero";
  let (xnum, xden) = to_zzfrac x in
  let (ynum, yden) = to_zzfrac y in
  ZZ.div (ZZ.mul xnum yden) (ZZ.mul ynum xden)

let modulo x y =
  if compare y zero = 0 then invalid_arg "QQ.modulo: divide by zero";
  let (xnum, xden) = to_zzfrac x in
  let (ynum, yden) = to_zzfrac y in
  of_zzfrac
    (ZZ.modulo (ZZ.mul xnum yden) (ZZ.mul ynum xden))
    (ZZ.mul xden yden)

let gcd x y =
  let (xnum, xden) = to_zzfrac x in
  let (ynum, yden) = to_zzfrac y in
  of_zzfrac (ZZ.gcd xnum ynum) (ZZ.lcm xden yden)

let lcm x y =
  let (xnum, xden) = to_zzfrac x in
  let (ynum, yden) = to_zzfrac y in
  of_zzfrac (ZZ.lcm xnum ynum) (ZZ.gcd xden yden)
