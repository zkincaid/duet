type t = Z.t

let pp = Z.pp_print
let show = Z.to_string

let hash = Z.hash

let compare = Z.compare
let equal x y = compare x y = 0
let leq x y = compare x y <= 0
let lt x y = compare x y < 0

let add = Z.add
let sub = Z.sub
let mul = Z.mul
let negate = Z.neg
let one = Z.one
let zero = Z.zero

let modulo = Z.erem
let div = Z.ediv
let div_rem = Z.ediv_rem

let fdiv = Z.fdiv
let cdiv = Z.cdiv
let frem x y = Z.sub x (Z.mul (Z.fdiv x y) y)
let crem x y = Z.sub x (Z.mul (Z.cdiv x y) y)

let gcd = Z.gcd
let lcm = Z.lcm

let of_int = Z.of_int
let of_string = Z.of_string

let to_int x = if Z.fits_int x then Some (Z.to_int x) else None

let min = Z.min
let max = Z.max
let abs = Z.abs

(* TODO: Z_mlgmpidl provides fast conversion *)
let mpz_of x = Mpzf.of_string (show x)
let of_mpz x = of_string (Mpzf.to_string x)
                         
