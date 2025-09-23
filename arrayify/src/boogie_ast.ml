type identifier = string

type typ =
  | Int
  | Array of typ


type binary_op =
  | Add
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

type unary_op =
  | Not
  | Neg

type expr =
  | LiteralInt of int
  | LiteralBool of bool
  | LiteralReal of float
  | Var of identifier
  | BinaryOp of binary_op * expr * expr
  | UnaryOp of unary_op * expr
  | FunctionCall of identifier * expr list
  | ArrayAccess of identifier * expr

type stmt =
  | Assign of identifier * expr
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
let body proc = proc.body 

type program = {
  globals : (identifier * typ) list;
  procedures : procedure list;
}

let rec string_of_typ = function
  | Int -> "int"
  | Array t -> "array of " ^ string_of_typ t

let string_of_binary_op = function
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Mod -> "%"
  | And -> "&&"
  | Or -> "||"
  | Eq -> "=="
  | Neq -> "!="
  | Lt -> "<"
  | Le -> "<="
  | Gt -> ">"
  | Ge -> ">="

let string_of_unary_op = function
  | Not -> "!"
  | Neg -> "-"

let rec string_of_expr = function
  | LiteralInt i -> string_of_int i
  | LiteralBool b -> string_of_bool b
  | LiteralReal r -> string_of_float r
  | Var id -> id
  | BinaryOp (op, e1, e2) ->
      "(" ^ string_of_expr e1 ^ " " ^ string_of_binary_op op ^ " " ^ string_of_expr e2 ^ ")"
  | UnaryOp (op, e) -> string_of_unary_op op ^ string_of_expr e
  | FunctionCall (id, args) ->
      id ^ "(" ^ String.concat ", " (List.map string_of_expr args) ^ ")"
  | ArrayAccess (id, index) ->
      id ^ "[" ^ string_of_expr index ^ "]"

let rec string_of_stmt = function
  | Assign (id, e) -> id ^ " := " ^ string_of_expr e ^ ";"
  | ArrayAssign (id, index, e) -> id ^ "[" ^ string_of_expr index ^ "] := " ^ string_of_expr e ^ ";"
  | Havoc id -> "havoc " ^ id ^ ";"
  | Assume e -> "assume " ^ string_of_expr e ^ ";"
  | Assert e -> "assert " ^ string_of_expr e ^ ";"
  | If (cond, then_stmts, else_stmts) ->
      "if (" ^ string_of_expr cond ^ ") {\n"
      ^ String.concat "\n" (List.map string_of_stmt then_stmts)
      ^ "\n} else {\n"
      ^ String.concat "\n" (List.map string_of_stmt else_stmts)
      ^ "\n}"
  | While (cond, body) ->
      "while (" ^ string_of_expr cond ^ ") {\n"
      ^ String.concat "\n" (List.map string_of_stmt body)
      ^ "\n}"
  | Call (id, args) ->
      id ^ "(" ^ String.concat ", " (List.map string_of_expr args) ^ ");"
  | Label id -> id ^ ":\n"
  | Goto id -> "goto " ^ id ^ ";"
  | Return -> "return;"

let string_of_param (id, t) = id ^ ": " ^ string_of_typ t

let string_of_procedure proc =
  "procedure " ^ proc.name ^ "("
  ^ String.concat ", " (List.map string_of_param proc.params)
  ^ ") returns ("
  ^ String.concat ", " (List.map string_of_param proc.returns)
  ^ ") {\n"
  ^ String.concat "\n" (List.map string_of_stmt proc.body)
  ^ "\n}"

let string_of_program prog =
  "globals:\n"
  ^ String.concat "\n" (List.map (fun (id, t) -> id ^ ": " ^ string_of_typ t) prog.globals)
  ^ "\n\nprocedures:\n"
  ^ String.concat "\n\n" (List.map string_of_procedure prog.procedures)