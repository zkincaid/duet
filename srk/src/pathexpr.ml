open BatHashcons

type 'a open_pathexpr =
  [ `Edge of int * int
  | `Mul of 'a * 'a
  | `Add of 'a * 'a
  | `Star of 'a
  | `Zero
  | `One ]

type 'a algebra = 'a open_pathexpr -> 'a

type pe =
  | Edge of int * int
  | Mul of t * t
  | Add of t * t
  | Star of t
  | One
  | Zero
and t = pe hobj

module HC = BatHashcons.MakeTable(struct
    type t = pe
    let equal x y = match x, y with
      | One, One | Zero, Zero -> true
      | Edge (s, t), Edge (s', t') -> s = s' && t = t'
      | Mul (s, t), Mul (s', t') -> s.tag = s'.tag && t.tag = t'.tag
      | Add (s, t), Add (s', t') -> s.tag = s'.tag && t.tag = t'.tag
      | Star t, Star t' -> t.tag = t'.tag
      | _ -> false
    let hash = function
      | Edge (x, y) -> Hashtbl.hash (0, x, y)
      | Mul (x, y) -> Hashtbl.hash (1, x.tag, y.tag)
      | Add (x, y) -> Hashtbl.hash (2, x.tag, y.tag)
      | Star x -> Hashtbl.hash (3, x.tag)
      | Zero -> Hashtbl.hash 4
      | One -> Hashtbl.hash 5
  end)
module HT = BatHashtbl.Make(struct
    type t = pe hobj
    let equal s t = s.tag = t.tag
    let hash t = t.hcode
  end)

type context = HC.t
type 'a table = 'a HT.t

let mk_one pe = HC.hashcons pe One
let mk_zero pe = HC.hashcons pe Zero
let mk_mul pe x y = match x.obj, y.obj with
  | Zero, _ | _, Zero -> mk_zero pe
  | One, _ -> y
  | _, One -> x
  | _, _ ->
    HC.hashcons pe (Mul (x, y))
let mk_add pe x y = match x.obj, y.obj with
  | Zero, _ -> y
  | _, Zero -> x
  | _, _ -> HC.hashcons pe (Add (x, y))
let mk_star pe x = HC.hashcons pe (Star x)
let mk_edge pe src tgt = HC.hashcons pe (Edge (src, tgt))

let rec pp formatter pathexpr =
  let open Format in
  match pathexpr.obj with
  | Edge (x, y) -> fprintf formatter "@[%d->%d@]" x y
  | Mul (x, y) -> fprintf formatter "@[(%a)@ . (%a)@]" pp x pp y
  | Add (x, y) -> fprintf formatter "@[%a@ + %a@]" pp x pp y
  | Star x -> fprintf formatter "@[(%a)*@]" pp x
  | Zero -> fprintf formatter "0"
  | One -> fprintf formatter "1"

let mk_table ?(size=991) () = HT.create size      
let mk_context ?(size=991) () = HC.create size

let eval ?(table=HT.create 991) (f : 'a open_pathexpr -> 'a) =
  let rec go expr =
    if HT.mem table expr then
      HT.find table expr
    else
      let result =
        match expr.obj with
        | One -> f `One
        | Zero -> f `Zero
        | Mul (x, y) -> f (`Mul (go x, go y))
        | Add (x, y) -> f (`Add (go x, go y))
        | Star x -> f (`Star (go x))
        | Edge (s, t) -> f (`Edge (s, t))
      in
      HT.add table expr result;
      result
  in
  go

let forget table p =
  let safe = eval (function
      | `One | `Zero -> true
      | `Edge (s, t) -> p s t
      | `Mul (x, y) | `Add (x, y) -> x && y
      | `Star x -> x)
  in
  HT.filteri_inplace (fun k _ -> safe k) table
