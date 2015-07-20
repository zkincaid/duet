open Apak
type t = Mpqf.t

let opt_default_accuracy = ref (-1)

let pp = Mpqf.print
let show = Putil.mk_show pp

let compare = Mpqf.cmp
let equal = Mpqf.equal
let leq x y = compare x y <= 0
let lt x y = compare x y < 0

let add = Mpqf.add
let sub = Mpqf.sub
let mul = Mpqf.mul
let zero = Mpqf.of_int 0
let one = Mpqf.of_int 1

let div x y =
  if compare y zero = 0 then invalid_arg "QQ.div: divide by zero"
  else Mpqf.div x y

let negate = Mpqf.neg
let inverse = Mpqf.inv

let of_int = Mpqf.of_int
let of_zz = Mpqf.of_mpz
let of_frac = Mpqf.of_frac
let of_zzfrac = Mpqf.of_mpz2
let of_float = Mpqf.of_float
let of_string = Mpqf.of_string
let to_zzfrac = Mpqf.to_mpzf2

let to_zz qq =
  let (num, den) = to_zzfrac qq in
  if Mpz.cmp den (Mpzf.of_int 1) == 0 then Some num
  else None
let to_float qq = Mpqf.to_float qq

let numerator = Mpqf.get_num
let denominator = Mpqf.get_den
let hash x = Hashtbl.hash (Mpqf.to_string x)

let exp x k =
  let rec go x k =
    if k = 0 then one
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

let min x y = if leq x y then x else y
let max x y = if leq x y then y else x
let abs = Mpqf.abs

(* Truncated continued fraction *)
let rec nudge ?(accuracy=(!opt_default_accuracy)) x =
  if accuracy < 0 then
    (x, x)
  else
    let (num, den) = to_zzfrac x in
    let (q, r) = Mpzf.fdiv_qr num den in
    if accuracy = 0 then
      (Mpqf.of_mpz q, Mpqf.of_mpz (Mpzf.add_int q 1))
    else if Mpzf.cmp_int r 0 = 0 then
      (of_zz q, of_zz q)
    else
      let (lo, hi) = nudge ~accuracy:(accuracy - 1) (of_zzfrac den r) in
      (add (of_zz q) (inverse hi),
       add (of_zz q) (inverse lo))

let rec nudge_down ?(accuracy=(!opt_default_accuracy)) x =
  if accuracy < 0 then
    x
  else
    let (num, den) = to_zzfrac x in
    let (q, r) = Mpzf.fdiv_qr num den in
    if accuracy = 0 then
      Mpqf.of_mpz q
    else if Mpzf.cmp_int r 0 = 0 then
      of_zz q
    else
      let hi = nudge_up ~accuracy:(accuracy - 1) (of_zzfrac den r) in
      add (of_zz q) (inverse hi)
and nudge_up ?(accuracy=(!opt_default_accuracy)) x =
  if accuracy < 0 then
    x
  else
    let (num, den) = to_zzfrac x in
    let (q, r) = Mpzf.fdiv_qr num den in
    if accuracy = 0 then
      Mpqf.of_mpz (Mpzf.add_int q 1)
    else if Mpzf.cmp_int r 0 = 0 then
      of_zz q
    else
      let lo = nudge_down ~accuracy:(accuracy - 1) (of_zzfrac den r) in
      add (of_zz q) (inverse lo)

let floor x =
  let (num, den) = to_zzfrac x in
  Mpzf.fdiv_q num den

let idiv x y =
  let (xnum, xden) = to_zzfrac x in
  let (ynum, yden) = to_zzfrac y in
  ZZ.div (ZZ.mul xnum yden) (ZZ.mul ynum xden)

let modulo x y =
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
