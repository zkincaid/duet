open BatPervasives

type t =
  { lower : QQ.t option;
    upper : QQ.t option }
    [@@deriving ord]

let pp formatter x =
  Format.fprintf
    formatter
    "[%s, %s]"
    (match x.lower with
     | Some lo -> QQ.show lo
     | None -> "-oo")
    (match x.upper with
     | Some hi -> QQ.show hi
     | None -> "+oo")

let show = SrkUtil.mk_show pp

let bottom = { lower = Some QQ.one; upper = Some QQ.zero }
let top = { lower = None; upper = None }
let const k = { lower = Some k; upper = Some k }
let zero = const QQ.zero
let one = const QQ.one
let normalize x =
  match x.lower, x.upper with
  | (Some lo, Some hi) when QQ.lt hi lo -> bottom
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
  if equal x bottom then
    bottom
  else if QQ.equal k QQ.zero then
    zero
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

let widening x y =
  let y = join x y in
  normalize {
    lower =
      begin match x.lower, y.lower with
        | Some x, Some y when QQ.equal x y -> Some x
        | _ -> None
      end;
    upper =
      begin match x.upper, y.upper with
        | Some x, Some y when QQ.equal x y -> Some x
        | _ -> None
      end
  }

(* Is every member of the interval x inside the interval y? *)
let leq x y = equal x (meet x y)

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
    (* TODO: this is a coarse abstraction *)
    let y_1 = map_opt (flip QQ.sub QQ.one) y.upper in (* |y|-1 *)
    let divisor_ivl = { lower = Some QQ.zero; upper = y_1 } in
    divisor_ivl

let upper x = x.upper
let lower x = x.lower
let floor x =
  { lower = map_opt (QQ.of_zz % QQ.floor) x.lower;
    upper = map_opt (QQ.of_zz % QQ.floor) x.upper }

let of_apron ivl =
  let cvt scalar =
    if Apron.Scalar.is_infty scalar == 0
    then Some (SrkApron.qq_of_scalar scalar)
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

let integral x =
  { lower = map_opt (QQ.of_zz % QQ.ceiling) x.lower;
    upper = map_opt (QQ.of_zz % QQ.floor) x.upper }

let log base x =
  if equal base bottom || equal x bottom then bottom
  else
    match base.lower with
    | Some base_lo when QQ.lt QQ.one base_lo ->
      (* Naive integral lower/upper approximation of log.  TODO: make this
         more accurate. *)
      let lower =
        match base.upper, x.lower with
        | Some base, Some lo when QQ.leq QQ.one lo ->
          let rec lo_log curr log =
            if log > 32 then
              None
            else if QQ.lt lo curr then
              Some (QQ.of_int (log - 1))
            else
              lo_log (QQ.mul base curr) (log + 1)
          in
          lo_log base 1
        | _, _ -> None
      in
      let upper =
        match x.upper with
        | Some hi when QQ.leq QQ.one hi  ->
          let rec hi_log curr log =
            if log > 32 then
              None
            else if QQ.leq hi curr then
              Some (QQ.of_int log)
            else
              hi_log (QQ.mul base_lo curr) (log + 1)
          in
          (hi_log QQ.one 0)
        | _ -> None
      in
      { lower; upper }
    | _ -> top

let rec exp_const ivl n =
  if n = 0 then one
  else if n = 1 then ivl
  else begin
    let q = exp_const ivl (n / 2) in
    let q_squared =
      meet (mul q q) (make (Some QQ.zero) None)
    in
    if n mod 2 = 0 then q_squared
    else mul q q_squared
  end

let exp base exponent =
  let (>>/) a f = BatOption.map f a in
  let (>>=) a f = BatOption.Monad.bind a f in
  if is_nonnegative exponent then
    match base.lower, base.upper with
    | Some base_lo, Some base_hi when QQ.leq QQ.one base_lo ->
      (* base^exp is monotone *)
      { lower = lower exponent >>/ QQ.floor >>= ZZ.to_int >>/ QQ.exp base_lo;
        upper = upper exponent >>/ QQ.floor >>= ZZ.to_int >>/ QQ.exp base_hi }

    | Some base_lo, Some base_hi when QQ.leq QQ.zero base_lo && QQ.leq base_hi QQ.one ->
      (* base^exp is antitone *)
      let lo =
        match upper exponent >>/ QQ.ceiling >>= ZZ.to_int >>/ QQ.exp base_lo with
        | Some lo -> Some lo
        | None -> Some QQ.zero
      in
      { lower = lo;
        upper = lower exponent >>/ QQ.floor >>= ZZ.to_int >>/ QQ.exp base_lo }
    | _ -> top
  else if is_nonnegative base then
    { lower = Some QQ.zero;
      upper = None }
  else
    top
