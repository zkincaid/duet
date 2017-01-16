(* Global types *)

type vtype =
  | Int of int
  | Void
  | Unknown
  | Pointer of vtype
  | Array of vtype

type variable =
  | Var of string * vtype
  | Constant of int * int

type binop =
  | Add
  | Sub
  | Mult
  | Div
  | Rem
  | LShift
  | RShift
  | BXor
  | BAnd
  | BOr


type lsum =
  | LExpr of lsum * binop * lsum
  | UNeg of lsum
  | LVal of variable
  | LNeg of lsum
  | ArrayAccess of variable * lsum
  | Havoc

type cop =
  | GTE
  | GT
  | LTE
  | LT
  | NE
  | EQ

type cond = Cond of lsum * cop * lsum | NonDet | Jmp


(* Control flow graphs for CS IR *)

type branch =
  | Branch of int list
  | Return of variable option

type inst =
  | Assign of lsum * lsum
  | BinExpr of lsum * lsum * binop * lsum
  | Call of lsum option * string * lsum list
  | Tick of lsum * lsum
  | Assert of cond * string
  | Assume of cond

type bblock =
  { bpreds: int list
  ; binsts: inst list
  ; btype: branch
  ; bcond: cond option
  }


(* Functions *)

type func =
  { fname: string
  ; fargs: variable list
  ; flocs: variable list
  ; fbody: bblock array
  ; fret: variable option
  }
