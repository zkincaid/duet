open Ark
open ArkPervasives

(* Ocaml definition of an imperative language *)

(* Type definition for AST nodes *)

type aexp_type = 
  Real_const of QQ.t
| Sum_exp of (aexp_type * aexp_type)
| Diff_exp of (aexp_type * aexp_type)
| Mult_exp of (aexp_type * aexp_type) 
| Var_exp of string
| Unneg_exp of aexp_type 
| Havoc_aexp

type bexp_type = 
  Bool_const of bool
| Eq_exp of (aexp_type * aexp_type)
| Ne_exp of (aexp_type * aexp_type)
| Gt_exp of (aexp_type * aexp_type)
| Lt_exp of (aexp_type * aexp_type)
| Ge_exp of (aexp_type * aexp_type)
| Le_exp of (aexp_type * aexp_type)
| And_exp of (bexp_type * bexp_type)
| Not_exp of bexp_type
| Or_exp of (bexp_type * bexp_type)
| Havoc_bexp

      
type stmt_type = 
   Skip 
|  Assign of (string * aexp_type) 
| Seq of (stmt_type * stmt_type)
| Ite of (bexp_type * stmt_type * stmt_type)
| While of (bexp_type * stmt_type * bool)
| Assert of bexp_type
| Print of aexp_type
| Assume of bexp_type



type prog_type = 
  Prog of stmt_type  

let rec aexp_to_string e =
  match e with
    Real_const r -> (QQ.show r)
  | Var_exp x -> x
  | Mult_exp (e1, e2) ->
    String.concat ""
      ["("; aexp_to_string e1; " * ";
       aexp_to_string e2; ")"]
  | Sum_exp (e1, e2) ->
    String.concat ""
      ["("; aexp_to_string e1; " + ";
       aexp_to_string e2; ")"]
  | Diff_exp (e1, e2) ->
    String.concat ""
      ["("; aexp_to_string e1; " - ";
       aexp_to_string e2; ")"]
  | Unneg_exp (e1) ->
    String.concat ""
      ["(-";
       aexp_to_string e1; ")"]
  | Havoc_aexp -> "nondet()"

and
aexp_list_to_string lst =
  match lst with
    [] -> ""
  | [x] -> aexp_to_string x
  | head :: rest ->
    String.concat ""
      [aexp_to_string head;
       ", ";
       aexp_list_to_string rest]

let rec bexp_to_string b =
  match b with
  | Bool_const (true) -> " 0 <= 0"
  | Bool_const (false) -> " 1 <= 0"
  | Gt_exp (e1, e2) ->
    String.concat ""
      [aexp_to_string e1; " > ";
       aexp_to_string e2]
  | Lt_exp (e1, e2) ->
    String.concat ""
      [aexp_to_string e1; " < ";
       aexp_to_string e2]
  | Ge_exp (e1, e2) ->
    String.concat ""
      [aexp_to_string e1; " >= ";
       aexp_to_string e2]
  | Le_exp (e1, e2) ->
    String.concat ""
      [aexp_to_string e1; " <= ";
       aexp_to_string e2]
  | Eq_exp (e1, e2) ->
     String.concat ""
      [aexp_to_string e1; " == ";
       aexp_to_string e2]
  | Ne_exp (e1, e2) ->
     String.concat ""
      [aexp_to_string e1; " != ";
       aexp_to_string e2]
  | And_exp (b1, b2) ->
    String.concat ""
      ["("; bexp_to_string b1; " && ";
       bexp_to_string b2; ")"]
  | Not_exp b1  ->
    String.concat ""
      ["!("; bexp_to_string b1; ")"]
  | Or_exp (b1, b2) ->
    String.concat ""
      ["("; bexp_to_string b1; " || ";
       bexp_to_string b2; ")"]
  | Havoc_bexp -> "nondet() < 1"

let rec stmt_to_string s =
  match s with
    Skip -> "skip"
  | Assign (var, e) ->
    String.concat "" [var; " := "; aexp_to_string e]
  | Seq (s1, s2) ->
    (match s1 with
      Skip -> (stmt_to_string s2)
    | _  ->
          (match s2 with
         Skip -> (stmt_to_string s1)
          | _ -> (String.concat "" [stmt_to_string s1; ";\n"; stmt_to_string s2])))
  | Ite (b, s1, s2) ->
    String.concat ""
      ["if ("; (bexp_to_string b); ") { \n";
       stmt_to_string s1; "\n}\nelse { \n";
       stmt_to_string s2; "\n}"]
  | While (b, s1, false) ->
    String.concat ""
      ["while ("; bexp_to_string b; ") { \n";
       stmt_to_string s1; "\n}\n"]
  | While (b, s1, true) ->
    String.concat ""
      ["residual-while ("; bexp_to_string b; ") { \n";
       stmt_to_string s1; "\n}\n"]
  | Print(e) ->
    String.concat ""
      ["print ("; aexp_to_string e; ")\n"]
  | Assert b ->
    String.concat ""
      ["assert ("; bexp_to_string b; ")"]
  | Assume b ->
    String.concat ""
      ["assume ("; bexp_to_string b; ")"]
