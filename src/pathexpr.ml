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
  | Omega of t
and t = pe hobj

(* Path expressions & omega path expressions are represented by the
   same type.  The type equality is not exported, and well-formedness
   of (omega) path expressions is enforced by the structure of the
   module. *)
type omega = t

type ('a,'b) open_omega_pathexpr =
  [ `Omega of 'a
  | `Mul of 'a * 'b
  | `Add of 'b * 'b ]

type ('a,'b) omega_algebra = ('a,'b) open_omega_pathexpr -> 'b

module HC = BatHashcons.MakeTable(struct
    type t = pe
    let equal x y = match x, y with
      | One, One | Zero, Zero -> true
      | Edge (s, t), Edge (s', t') -> s = s' && t = t'
      | Mul (s, t), Mul (s', t') -> s.tag = s'.tag && t.tag = t'.tag
      | Add (s, t), Add (s', t') -> s.tag = s'.tag && t.tag = t'.tag
      | Star t, Star t' -> t.tag = t'.tag
      | Omega t, Omega t' -> t.tag = t'.tag
      | _ -> false
    let hash = function
      | Edge (x, y) -> Hashtbl.hash (0, x, y)
      | Mul (x, y) -> Hashtbl.hash (1, x.tag, y.tag)
      | Add (x, y) -> Hashtbl.hash (2, x.tag, y.tag)
      | Star x -> Hashtbl.hash (3, x.tag)
      | Omega x -> Hashtbl.hash (4, x.tag)
      | Zero -> Hashtbl.hash 5
      | One -> Hashtbl.hash 6
  end)
module HT = BatHashtbl.Make(struct
    type t = pe hobj
    let equal s t = s.tag = t.tag
    let hash t = t.hcode
  end)

type context = HC.t
type 'a table = 'a HT.t
type ('a,'b) omega_table = ('a table * 'b HT.t)

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
let mk_star pe x = match x.obj with
  | Zero | One -> mk_one pe
  | Star _ -> x
  | _ -> HC.hashcons pe (Star x)
let mk_edge pe src tgt = HC.hashcons pe (Edge (src, tgt))

let mk_omega pe x = HC.hashcons pe (Omega x)
let mk_omega_add = mk_add
let mk_omega_mul = mk_mul

let destruct_flat p =
  let rec destruct_mul p =
    match p.obj with
    | Mul (p1, p2) -> (destruct_mul p1) @ (destruct_mul p2)
    | _ -> [p]
  in
  let rec destruct_add p =
    match p.obj with
    | Add (p1, p2) -> (destruct_add p1) @ (destruct_add p2)
    | _ -> [p]
  in
  match p.obj with
  | Edge (x, y) -> `Edge (x, y)
  | Add (p1, p2) -> `Add ((destruct_add p1) @ (destruct_add p2))
  | Mul (p1, p2) -> `Mul ((destruct_mul p1) @ (destruct_mul p2))
  | Star p' -> `Star p'
  | Omega p' -> `Omega p'
  | One -> `One
  | Zero -> `Zero

let rec pp formatter pathexpr =
  let open Format in
  match destruct_flat pathexpr with
  | `Edge (x, y) -> fprintf formatter "@[%d->%d@]" x y
  | `Mul ps ->
     pp_open_hovbox formatter 1;
     pp_print_list ~pp_sep:pp_print_space pp formatter ps;
     pp_close_box formatter ()
  | `Add ps ->
     let pp_sep formatter () = fprintf formatter "@,+ " in
     pp_open_hovbox formatter 1;
     pp_print_list ~pp_sep pp formatter ps;
     pp_close_box formatter ()
  | `Star x -> fprintf formatter "@[(%a)*@]" pp x
  | `Omega x -> fprintf formatter "@[(%a)w@]" pp x
  | `Zero -> fprintf formatter "0"
  | `One -> fprintf formatter "1"

let pp_omega = pp

let show = SrkUtil.mk_show pp
let show_omega = show

let mk_table ?(size=991) () = HT.create size
let mk_context ?(size=991) () = HC.create size
let mk_omega_table ?(size=991) table = (table, HT.create size)

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
        | Omega _ -> assert false
      in
      HT.add table expr result;
      result
  in
  go

let eval_omega
      ?(table=(HT.create 991,HT.create 991))
      (f : 'a algebra)
      (g : ('a,'b) omega_algebra) =
  let (table, omega_table) = table in
  let rec go expr =
    if HT.mem omega_table expr then
      HT.find omega_table expr
    else
      let result =
        match expr.obj with
        | Omega x -> g (`Omega (eval ~table f x))
        | Add (x, y) -> g (`Add (go x, go y))
        | Mul (x, y) -> g (`Mul (eval ~table f x, go y))
        | _ -> assert false
      in
      HT.add omega_table expr result;
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

let rec accept_epsilon p =
  match p.obj with
  | Zero -> false
  | One -> true
  | Edge (_, _) -> false
  | Mul (x, y) -> accept_epsilon x && accept_epsilon y
  | Add (x, y) -> accept_epsilon x || accept_epsilon y
  | Star _ -> true
  | Omega _ -> false

module EdgeSet = BatSet.Make(struct
                     type t = int * int [@@deriving ord]
                   end)

let rec first p = match p.obj with
  | Zero | One -> EdgeSet.empty
  | Edge (x,y) -> EdgeSet.singleton (x,y)
  | Mul (p1, p2) ->
     if accept_epsilon p1 then
       EdgeSet.union (first p1) (first p2)
     else
       first p1
  | Add (p1, p2) -> EdgeSet.union (first p1) (first p2)
  | Star p' | Omega p' -> first p'

let rec derivative pe e p =
  match p.obj with
  | Zero -> mk_zero pe
  | One -> mk_zero pe
  | Edge (x,y) when (x,y) == e -> mk_one pe
  | Edge (_,_) -> mk_zero pe
  | Mul (p1, p2) ->
     let d = mk_mul pe (derivative pe e p1) p2 in
     if accept_epsilon p1 then
       mk_add pe d (derivative pe e p2)
     else d
  | Star p' ->
     mk_mul pe (derivative pe e p') p
  | Add (p1, p2) ->
     mk_add pe (derivative pe e p1) (derivative pe e p2)
  | Omega p' ->
     mk_mul pe (derivative pe e p') p

module PairHT = BatHashtbl.Make(struct
                    type t = (pe hobj) * (pe hobj)
                    let equal (s1,s2) (t1,t2) =
                      s1.tag = t1.tag && t2.tag = s2.tag
                    let hash (t1,t2) = Hashtbl.hash (t1.hcode, t2.hcode)
                  end)

let equiv pe p1 p2 =
  let visited = PairHT.create 991 in
  let rec equiv p1 p2 =
    PairHT.mem visited (p1,p2)
    || ((accept_epsilon p1) = (accept_epsilon p2)
        && let first1, first2 = first p1, first p2 in
           EdgeSet.equal first1 first2
           && (EdgeSet.for_all
                 (fun e -> equiv (derivative pe e p1) (derivative pe e p2))
                 first1))
  in
  equiv p1 p2
