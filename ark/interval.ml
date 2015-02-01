open BatPervasives
open Apak
open ArkPervasives

type interval =
  { lower : QQ.t option;
    upper : QQ.t option }
    deriving (Compare)

module Show_interval = Deriving_Show.Defaults(struct
  type a = interval
  let format formatter x =
    Format.fprintf formatter "[%s, %s]"
      (match x.lower with
      | Some lo -> QQ.show lo
      | None -> "-oo")
      (match x.upper with
      | Some hi -> QQ.show hi
      | None -> "+oo")
end)
let format = Show_interval.format
let show = Show_interval.show


let compare = Compare_interval.compare
let bottom = { lower = Some QQ.one; upper = Some QQ.zero }
let top = { lower = None; upper = None }
let const k = { lower = Some k; upper = Some k }
let zero = const QQ.zero
let normalize x =
  match x.lower, x.upper with
  | (Some lo, Some hi) when QQ.gt lo hi -> bottom
  | (_, _) -> x

let make_bounded lo hi = normalize { lower = Some lo; upper = Some hi }
let make lo hi = normalize { lower = lo; upper = hi }

let negate x =
  let neg = function
    | Some a -> Some (QQ.negate a)
    | None   -> None
  in
  { lower = neg x.upper; upper = neg x.lower }
let equal x y = compare x y = 0

let map_opt f x = match x with
  | Some x -> Some (f x)
  | None   -> None

let add x y =
  if equal x bottom || equal y bottom then bottom else
    let lower = match x.lower, y.lower with
      | Some a, Some b -> Some (QQ.add a b)
      | _, _ -> None
    in
    let upper = match x.upper, y.upper with
      | Some a, Some b -> Some (QQ.add a b)
      | _, _ -> None
    in
    { lower = lower; upper = upper }

let mul_const k x =
  if equal x bottom then bottom
  else if QQ.lt k QQ.zero then begin
    { lower = map_opt (QQ.mul k) x.upper;
      upper = map_opt (QQ.mul k) x.lower }
  end else begin
    { lower = map_opt (QQ.mul k) x.lower;
      upper = map_opt (QQ.mul k) x.upper }
  end

let join x y =
  if equal x bottom then y
  else if equal y bottom then x
  else {
    lower =
      begin match x.lower, y.lower with
	    | Some x, Some y -> Some (QQ.min x y)
	    | _, _ -> None
      end;
    upper =
      begin match x.upper, y.upper with
	    | Some x, Some y -> Some (QQ.max x y)
	    | _, _ -> None
      end
  }

let widen x y =
  if equal x bottom then y
  else
    let y = join x y in
    let lower = match x.lower, y.lower with
      | Some x, Some y when QQ.equal x y -> Some x
      | _, _ -> None
    in
    let upper = match x.upper, y.upper with
      | Some x, Some y when QQ.equal x y -> Some x
      | _, _ -> None
    in
    { lower; upper }

let meet x y = normalize {
  lower =
    begin match x.lower, y.lower with
    | None, x | x, None -> x
    | Some x, Some y -> Some (QQ.max x y)
    end;
  upper =
    begin match x.upper, y.upper with
    | None, x | x, None -> x
    | Some x, Some y -> Some (QQ.min x y)
    end
}

(* Is every member of the interval x inside the interval y? *)
let leq x y = equal x (meet x y)

(* Is every member of the interval x <= every member of the interval y? *)
let left x y =
  match x.upper, y.lower with
  | (Some x_hi, Some y_lo) -> QQ.leq x_hi y_lo
  | (_, _) -> false

(* Is every member of the interval x < every member of the interval y? *)
let strictly_left x y =
  match x.upper, y.lower with
  | (Some x_hi, Some y_lo) -> QQ.lt x_hi y_lo
  | (_, _) -> false

let is_nonnegative x =
  match x.lower with
  | None    -> false
  | Some lo -> QQ.leq QQ.zero lo

let is_nonpositive x =
  match x.upper with
  | None    -> false
  | Some hi -> QQ.leq hi QQ.zero

let is_positive x =
  match x.lower with
  | None    -> false
  | Some lo -> QQ.lt QQ.zero lo

let is_negative x =
  match x.upper with
  | None    -> false
  | Some hi -> QQ.lt hi QQ.zero

let elem a x =
  begin match x.lower with
  | Some b -> QQ.leq b a
  | None -> true
  end && begin match x.upper with
  | Some b -> QQ.leq a b
  | None -> true
  end

let mul x y =
  if equal x bottom || equal y bottom then bottom
  else if equal x zero || equal y zero then zero else begin
    match x.lower, x.upper with
    | Some a, Some b -> join (mul_const a y) (mul_const b y)
    | None, None -> top
    | None, Some a ->
      if is_nonnegative y then
	{ lower = None; upper = (mul_const a y).upper }
      else if is_nonpositive y then
	{ lower = (mul_const a y).lower; upper = None }
      else top
    | Some a, None ->
      if is_nonpositive y then
	{ lower = None; upper = (mul_const a y).upper }
      else if is_nonnegative y then
	{ lower = (mul_const a y).lower; upper = None }
      else top
  end

let div x y =
  if equal x bottom || equal y bottom then bottom
  else begin match y.lower, y.upper with
  | Some a, Some b ->
    if elem QQ.zero y then top
    else join (mul_const (QQ.inverse a) x) (mul_const (QQ.inverse b) x)
  | _, _ -> top (* todo *)
  end

let abs x =
  if is_nonnegative x then x
  else if is_nonpositive x then negate x
  else
    let upper =
      match x.lower, x.upper with
      | (Some lo, Some hi) -> Some (QQ.max (QQ.negate lo) hi)
      | (_, _) -> None
    in
    { lower = Some QQ.zero; upper = upper }

let modulo x y =
  if equal x bottom || equal y bottom then
    bottom
  else if elem QQ.zero y then top
  else
    (* mod y is the same as mod |y| *)
    let y = abs y in
    match y.lower with
    (* |y| is sufficiently large for "mod y" be a no-op on x *)
    | Some lo when strictly_left (abs x) (const lo) -> x
    | _ ->
       let y_1 = map_opt (flip QQ.sub QQ.one) y.upper in (* |y|-1 *)
       let divisor_ivl = { lower = map_opt QQ.negate y_1; upper = y_1 } in
       let dividend_ivl = join x zero in
       meet divisor_ivl dividend_ivl

let upper x = x.upper
let lower x = x.lower
let floor x =
  { lower = map_opt (QQ.of_zz % QQ.floor) x.lower;
    upper = map_opt (QQ.of_zz % QQ.floor) x.upper }

let of_apron ivl =
  let cvt scalar =
    if Apron.Scalar.is_infty scalar == 0
    then Some (NumDomain.qq_of_scalar scalar)
    else None
  in
  make (cvt ivl.Apron.Interval.inf) (cvt ivl.Apron.Interval.sup)

let apron_of { lower; upper } =
  let lo = match lower with
    | Some lo -> Apron.Scalar.of_mpqf lo
    | None -> Apron.Scalar.of_infty (-1)
  in
  let hi = match upper with
    | Some hi -> Apron.Scalar.of_mpqf hi
    | None -> Apron.Scalar.of_infty 1
  in
  Apron.Interval.of_scalar lo hi

let const_of { lower; upper } =
  match upper, lower with
  | Some hi, Some lo when QQ.equal hi lo -> Some hi
  | _ -> None

let nudge ?(accuracy=(!ArkPervasives.opt_default_accuracy)) {lower; upper} =
  { lower = map_opt (QQ.nudge_down ~accuracy:accuracy) lower;
    upper = map_opt (QQ.nudge_up ~accuracy:accuracy) upper }
