type identifier = string
type typ = Int | Array of typ
type binary_op =
    Add
  | Sub
  | Mul
  | Div
  | Mod
  | And
  | Or
  | Eq
  | Neq
  | Lt
  | Le
  | Gt
  | Ge
type unary_op = Not | Neg
type expr =
    LiteralInt of int
  | LiteralBool of bool
  | LiteralReal of float
  | Var of identifier
  | BinaryOp of binary_op * expr * expr
  | UnaryOp of unary_op * expr
  | FunctionCall of identifier * expr list
  | ArrayAccess of identifier * expr
type stmt =
    Assign of identifier * expr
  | ArrayAssign of identifier * expr * expr
  | Havoc of identifier
  | Assume of expr
  | Assert of expr
  | If of expr * stmt list * stmt list
  | While of expr * stmt list
  | Call of identifier * expr list
  | Label of identifier
  | Goto of identifier
  | Return
type param = identifier * typ
type procedure = {
  name : identifier;
  params : param list;
  locals : param list;
  returns : param list;
  body : stmt list;
}
val body : procedure -> stmt list
type program = {
  globals : (identifier * typ) list;
  procedures : procedure list;
}
val string_of_typ : typ -> string
val string_of_binary_op : binary_op -> string
val string_of_unary_op : unary_op -> string
val string_of_expr : expr -> identifier
val string_of_stmt : stmt -> string
val string_of_param : string * typ -> string
val string_of_procedure : procedure -> string
val string_of_program : program -> string
