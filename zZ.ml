open Apak

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

let hash x = Hashtbl.hash (Mpzf.to_string x)

let compare = Compare_t.compare
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

let floor_div = Mpzf.fdiv_q

let gcd = Mpzf.gcd
let lcm = Mpzf.lcm

let of_int = Mpzf.of_int
let of_string = Mpzf.of_string

let to_int x =
  if Mpz.fits_int_p x then Some (Mpz.get_int x) else None

let min x y = if leq x y then x else y
let max x y = if geq x y then x else y
