(* Global types *)

type vtype =
  | Int of int
  | Unknown
  (* | Array of vtype *)
  | Record of string

type variable= (string * vtype)
type lvalue =
  | Var of variable
  | Undef
  | FieldAccess of lvalue * string

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

type unop=
  | UNeg
  | LNeg

type rexpr =
  | Constant of int * int
  | LVal of lvalue
  | BExpr of rexpr * binop * rexpr
  | UExpr of unop * rexpr
  | Multiple of rexpr list


type cop =
  | GTE
  | GT
  | LTE
  | LT
  | NE
  | EQ

type cond = Cond of rexpr * cop * rexpr | NonDet | Jmp


(* Control flow graphs for CS IR *)

type branch =
  | Branch of int list
  | Return of variable list

type inst =
  | Assign of lvalue * rexpr
  | Call of lvalue list * string * rexpr list
  | Tick of rexpr
  | Assume of cond

type bblock =
  { bpreds: int list
  ; binsts: inst list
  ; btype: branch
  ; bcond: cond option
  }


(* Functions *)

type func =
  { funname: string
  ; fargs: variable list
  ; flocs: variable list
  ; fbody: bblock array
  ; frets: variable list
  }

exception Unexpected_value of string
