open Apak

type t = Mpzf.t

let pp = Mpzf.print
let show = Putil.mk_show pp

let hash x = Hashtbl.hash (Mpzf.to_string x)

let compare = Mpzf.cmp
let equal x y = compare x y = 0
let leq x y = compare x y <= 0
let lt x y = compare x y < 0
let geq x y = compare x y >= 0
let gt x y = compare x y > 0

let add = Mpzf.add
let sub = Mpzf.sub
let mul = Mpzf.mul
let negate = Mpzf.neg
let one = Mpzf.of_int 1
let zero = Mpzf.of_int 0

(* C99: a == (a/b)*b + a%b, division truncates towards zero *)
let modulo = Mpzf.tdiv_r
let div = Mpzf.tdiv_q

let gcd = Mpzf.gcd
let lcm = Mpzf.lcm

let of_int = Mpzf.of_int
let of_string = Mpzf.of_string

let to_int x =
  if Mpz.fits_int_p x then Some (Mpz.get_int x) else None

let min x y = if leq x y then x else y
let max x y = if geq x y then x else y
