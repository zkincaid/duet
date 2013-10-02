open Apak
open Buddy
open Graph

exception NotEqualConstants

type dkey = string
type rkey = string
type rel = rkey * (dkey list)
type var = string

type binary_operator =
    | OperatorUnion
    | OperatorIntersection
type set_relation =
    | SetSubset
    | SetEq
    | SetSuperset
type 'vartype arith_expr =
    | Atom of 'vartype
    | NegatedAtom of 'vartype
    | BinaryOp of binary_operator * 'vartype arith_expr * 'vartype arith_expr

let rec arith_expr_map mapper expr =
    let recurse = arith_expr_map mapper in
    match expr with
    | Atom x -> Atom (mapper x)
    | NegatedAtom x -> NegatedAtom (mapper x)
    | BinaryOp (a, b, c) -> BinaryOp (a, recurse b, recurse c)

type stmt =
    (* x = y *)
    | EQ of string * string
    (* x [not] in y *)
    | In of string * string arith_expr
    | Nin of string * string arith_expr
    (* x is <expr> *)
    | SetRelation of (set_relation * string * string arith_expr)
    (* [!] SomeRelation(a, ..., z) *)
    | Rel of var * (var list)
    | Neg of var * (var list)

(* <relation name> <parameters> <universally quantified variables> <body> *)
type rul = var * (var list) * (var list) * (stmt list) 

type program = {
        varorder: (string * int) list;
        domains: (string * int) list;
        domainpsets: (string * string) list;
        relations: rel list;
        input_rels: rkey list;
        output_rels: rkey list;
        rules: rul list}

(* Type of the new rules *)
type eq_var = Con of int | Var of int
type new_stmt =
    | R of string * eq_var list
    | N of string * eq_var list

type set_stmt =
    | StmtIn of (bool * eq_var * eq_var arith_expr) (* bool = if it's negated or not *)
    | StmtSetRelation of (set_relation * eq_var * eq_var arith_expr) (* assign from arithmetic statement *)

let ns_name = function R (x, _) | N (x, _) -> x
let ns_body = function R (_, y) | N (_, y) -> y

let string_of_binop v = assert false

let string_of_setrel x = match x with
    | SetSubset -> "is <="
    | SetEq -> "is"
    | SetSuperset -> "is >="

let string_of_eq_var v = match v with
    | Con x -> "Con "^(string_of_int x)
    | Var x -> "Var "^(string_of_int x)

let string_of_binop x = match x with
    | OperatorUnion -> "|"
    | OperatorIntersection -> "&"

let rec string_of_arith_expr exp = match exp with
    | Atom v -> string_of_eq_var v
    | NegatedAtom v -> "~" ^ (string_of_eq_var v)
    | BinaryOp (op, a, b) -> (string_of_arith_expr a)^(string_of_binop op)^(string_of_arith_expr b)

let string_of_set_stmt op = match op with
    | StmtIn (true, lhs, rhs) -> (string_of_eq_var lhs)^" in "^(string_of_arith_expr rhs)
    | StmtIn (false, lhs, rhs) -> (string_of_eq_var lhs)^" not in "^(string_of_arith_expr rhs)
    | StmtSetRelation (rel,lhs, rhs) -> (string_of_eq_var lhs)^" "^(string_of_setrel rel)^" "^(string_of_arith_expr rhs)

(* The type of the rule where the variables are renamed to bdd variables
but the rule has the datalog rule's structure.*)
type rnmed_rul = string * (eq_var list) * (new_stmt list)
type rnmed_rules = rnmed_rul list
type ae =
        | And of ae * ae
        | Exist of int * ae
        | Univ of int * ae
        | Stmt of new_stmt
        | Setop of set_stmt
        | Empty
type new_rul = string * (eq_var list) * ae
type new_rules = new_rul list

module StringMap = Map.Make(struct
			      type t = string
			      let compare = Pervasives.compare
			    end)

let find_canonical r canonicalforms =
   try StringMap.find r canonicalforms
   with Not_found -> failwith "Canonical form not set"

module OTString = struct
  type t = string
  let compare = Pervasives.compare
  let equal = Pervasives.(=)
  let hash = String.length
end

type state = bdd StringMap.t 
type canonicalforms = (int list) StringMap.t
type changed = bool StringMap.t

module New_rules = struct
  type t = new_rul
  let compare = Pervasives.compare
  let equal = Pervasives.(=)
  let hash = Hashtbl.hash
end 

let is_int x = 
  try ignore(int_of_string x); 
    true
  with _ -> false
;;
let is_int2 x = 
   try ignore(int_of_char x); 
       true
   with _ -> false
;;

module RuleMap = Map.Make(struct
			    type t = new_rul
			    let compare = Pervasives.compare
			  end)

type initial_state = bdd StringMap.t
type rules_bdds = bdd RuleMap.t

module HT = Hashtbl

(* (Global) domain information *)
type di = { dvars : ((string*int), int) HT.t; (* map (domain, integer) pairs
						 to fdd variables *)
            size : (string, int) HT.t (* map domains to their sizes *)} 
let dom_size domain di = HT.find di.size domain

let print_bdd_size bdd domains =
  let count = ref 0 in
  let f _ = incr count in
    fdd_allsat f bdd domains;
    print_endline ("Nodes: " ^ (string_of_int (bdd_nodecount bdd))
		   ^ " / Size: " ^ (string_of_int (!count)))

let format_term formatter  = function
  | Con x -> Format.fprintf formatter "Const %d" x
  | Var x -> Format.pp_print_int formatter x
let format_stmt formatter = function
  | R (x, vars) ->
    Format.fprintf formatter "%s%a" x (Putil.format_list format_term) vars
  | N (x, vars) ->
    Format.fprintf formatter "!%s%a" x (Putil.format_list format_term) vars
let rec format_arith_expr formatter = function
  | Atom x -> format_term formatter x
  | NegatedAtom x -> Format.fprintf formatter "~%a" format_term x
  | BinaryOp (op, x, y) ->
    Format.fprintf formatter "%s%a"
      (string_of_binop op)
      (Putil.format_list format_arith_expr) [x;y]
let format_set_stmt formatter = function
  | StmtIn (p, x, y) ->
    Format.fprintf formatter "%a@ %s@ %a"
      format_term x
      (if p then "in" else "not in")
      format_arith_expr y
  | StmtSetRelation (rel, x, y) ->
    Format.fprintf formatter "%a@ %s@ %a"
      format_term x
      (string_of_setrel rel)
      format_arith_expr y

let rec format_exp formatter = function
  | And (x, y) ->
    Format.fprintf formatter "%a,@,%a"
      format_exp x
      format_exp y
  | Empty -> ()
  | Exist (v, exp) ->
    Format.fprintf formatter "(@[exists %d.@ %a@])"
      v
      format_exp exp
  | Univ (v, exp) ->
    Format.fprintf formatter "(@[forall %d.@ %a@])"
      v
      format_exp exp
  | Stmt s -> format_stmt formatter s
  | Setop s -> format_set_stmt formatter s

let format_rule formatter (hd, vars, body) =
  Format.fprintf formatter "%s%a :- @[%a@]"
    hd
    (Putil.format_list format_term) vars
    format_exp body

(* Flatten a body into a list of literals *)
let rec flatten_body = function
  | And (x,y) -> (flatten_body x)@(flatten_body y)
  | Exist (_,x) | Univ (_,x) -> (flatten_body x)
  | Stmt x -> [x]
  | Setop x -> []
  | Empty -> []

module G = Persistent.Digraph.Concrete(OTString)
module K = Persistent.Digraph.Concrete(New_rules)
module T = Topological.Make(K)
module SCC = Components.Make(K)
module K_sub = ExtGraph.Subgraph(K)
