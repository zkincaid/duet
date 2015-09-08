open Ark
open ArkPervasives

(* Ocaml definition of an imperative language *)

(* Type definition for AST nodes *)

type aexp_type = 
    Real_const of QQ.t
  | Sum_exp of (aexp_type * aexp_type)
  | Diff_exp of (aexp_type * aexp_type)
  | Mult_exp of (aexp_type * aexp_type) 
  | Div_exp of (aexp_type * aexp_type) 
  | Var_exp of string
  | Unneg_exp of aexp_type 
  | Havoc_aexp
    deriving (Compare)

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
        deriving (Compare)

type cmd_type =
    Skip
  | Assign of (string * aexp_type) 
  | Assert of bexp_type
  | Print of aexp_type
  | Assume of bexp_type
        deriving (Compare)

type stmt_type = 
    Cmd of cmd_type
  | Seq of (stmt_type * stmt_type)
  | Ite of (bexp_type * stmt_type * stmt_type)
  | While of (bexp_type * stmt_type * bool)

type prog_type = 
    Prog of stmt_type

module Show_aexp_type = Deriving_Show.Defaults(struct
  type a = aexp_type
  let rec format formatter = function
    | Real_const r -> QQ.format formatter r
    | Var_exp x -> Format.pp_print_string formatter x
    | Sum_exp (a, b) ->
      Format.fprintf formatter "(%a + %a)" format a format b
    | Diff_exp (a, b) ->
      Format.fprintf formatter "(%a - %a)" format a format b
    | Mult_exp (a, b) ->
      Format.fprintf formatter "(%a * %a)" format a format b
    | Div_exp (a, b) ->
      Format.fprintf formatter "(%a / %a)" format a format b
    | Unneg_exp a ->
      Format.fprintf formatter "-(%a)" format a
    | Havoc_aexp -> Format.pp_print_string formatter "nondet()"
end)
module Show_bexp_type = Deriving_Show.Defaults(struct
  type a = bexp_type
  let fe = Show.format<aexp_type>
  let rec format formatter = function
    | Bool_const true -> Format.pp_print_string formatter "0 <= 0"
    | Bool_const false -> Format.pp_print_string formatter "1 <= 0"
    | Eq_exp (a, b) -> Format.fprintf formatter "%a == %a" fe a fe b
    | Ne_exp (a, b) -> Format.fprintf formatter "%a != %a" fe a fe b
    | Gt_exp (a, b) -> Format.fprintf formatter "%a > %a" fe a fe b
    | Lt_exp (a, b) -> Format.fprintf formatter "%a < %a" fe a fe b
    | Ge_exp (a, b) -> Format.fprintf formatter "%a >= %a" fe a fe b
    | Le_exp (a, b) -> Format.fprintf formatter "%a <= %a" fe a fe b
    | And_exp (phi,psi) ->
      Format.fprintf formatter "(%a && %a)" format phi format psi
    | Or_exp (phi,psi) ->
      Format.fprintf formatter "(%a || %a)" format phi format psi
    | Not_exp phi -> Format.fprintf formatter "!(%a)" format phi
    | Havoc_bexp -> Format.pp_print_string formatter "nondet() < 1"
end)
module Show_cmd_type = Deriving_Show.Defaults(struct
  type a = cmd_type
  let format formatter = function
    | Skip -> Format.pp_print_string formatter "skip"
    | Assign (v, rhs) ->
      Format.fprintf formatter "%s := %a" v Show.format<aexp_type> rhs
    | Assert phi ->
      Format.fprintf formatter "assert(%a)" Show.format<bexp_type> phi
    | Print t ->
      Format.fprintf formatter "print(%a)" Show.format<aexp_type> t
    | Assume phi ->
      Format.fprintf formatter "assume(%a)" Show.format<bexp_type> phi
end)
module Show_stmt_type = Deriving_Show.Defaults(struct
  type a = stmt_type
  let rec format formatter = function
    | Cmd c -> Show.format<cmd_type> formatter c
    | Seq (Cmd Skip, c) | Seq (c, Cmd Skip) -> format formatter c
    | Seq (c, d) ->
      Format.fprintf formatter "%a;@\n%a" format c format d
    | Ite (c, bthen, belse) ->
      Format.fprintf formatter "if (%a) {@\n  @[%a@]@\n} else {@\n  @[%a@]@\n}"
        Show.format<bexp_type> c
        format bthen
        format belse
    | While (c, body, _) ->
      Format.fprintf formatter "while (%a) {@\n  @[%a@]@\n}"
        Show.format<bexp_type> c
        format body
end)

let rec aexp_to_string e =
  match e with
    Real_const r -> (QQ.show r)
  | Var_exp x -> x
  | Mult_exp (e1, e2) ->
    String.concat ""
      ["("; aexp_to_string e1; " * ";
       aexp_to_string e2; ")"]
  | Div_exp (e1, e2) ->
    String.concat ""
      ["("; aexp_to_string e1; " / ";
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

(* Collecting variables *)

let rec collect_vars_aexp e =
  match e with
    Real_const m -> []
  | Sum_exp (e1, e2) -> (collect_vars_aexp e1) @ (collect_vars_aexp e2)
  | Diff_exp (e1, e2) -> (collect_vars_aexp e1) @ (collect_vars_aexp e2)
  | Mult_exp (e1, e2) -> (collect_vars_aexp e1) @ (collect_vars_aexp e2)
  | Div_exp (e1, e2) -> (collect_vars_aexp e1) @ (collect_vars_aexp e2)
  | Var_exp x -> [x]
  | Unneg_exp e1 -> (collect_vars_aexp e1)
  | Havoc_aexp -> []
and
  collect_vars_aexp_list l =
  match l with
    [] -> []
  | head :: rest -> (collect_vars_aexp head) @ (collect_vars_aexp_list rest)


let rec collect_vars_bexp b =
  match b with
    Bool_const bc -> []
  | Eq_exp (e1, e2) -> (collect_vars_aexp e1) @ (collect_vars_aexp e2)
  | Ne_exp (e1, e2) -> (collect_vars_aexp e1) @ (collect_vars_aexp e2)
  | Gt_exp (e1, e2) -> (collect_vars_aexp e1) @ (collect_vars_aexp e2)
  | Lt_exp (e1, e2) -> (collect_vars_aexp e1) @ (collect_vars_aexp e2)
  | Ge_exp (e1, e2) -> (collect_vars_aexp e1) @ (collect_vars_aexp e2)
  | Le_exp (e1, e2) -> (collect_vars_aexp e1) @ (collect_vars_aexp e2)
  | And_exp (b1, b2) -> (collect_vars_bexp b1) @ (collect_vars_bexp b2)
  | Not_exp b1 -> (collect_vars_bexp b1)
  | Or_exp  (b1, b2) -> (collect_vars_bexp b1) @ (collect_vars_bexp b2)
  | Havoc_bexp -> []


let collect_vars_cmd = function
  | Skip -> []
  | Assign (x, e) ->
    x :: (collect_vars_aexp e)
  | Assert (b) -> (collect_vars_bexp b)
  | Print (e) -> (collect_vars_aexp e)
  | Assume (b) -> (collect_vars_bexp b)

let rec collect_vars_stmt s =
  match s with
  | Cmd c -> collect_vars_cmd c
  | Seq (s1, s2) -> (collect_vars_stmt s1) @ (collect_vars_stmt s2)
  | Ite (b, s1, s2) -> (collect_vars_bexp b) @ (collect_vars_stmt s1) @ (collect_vars_stmt s2)
  | While (b, s1, _) -> (collect_vars_bexp b) @ (collect_vars_stmt s1)

let rec remove_dups l =
  match l with
    [] -> []
  | (x :: rest) ->
    if (List.mem x rest)
    then (remove_dups rest)
    else x :: (remove_dups rest)


let collect_vars s =
  let l = collect_vars_stmt s in
  remove_dups l

let primify x =
  String.concat "" [x;"\'"]

let unprimify x =
  assert (x.[String.length x - 1] = ''');
  String.sub x 0 (String.length x - 1)

let rec primify_aexp e =
  match e with
    Real_const m -> e
  | Sum_exp (e1, e2) -> Sum_exp (primify_aexp e1, primify_aexp e2)
  | Diff_exp (e1, e2) -> Diff_exp (primify_aexp e1, primify_aexp e2)
  | Mult_exp (e1, e2) -> Mult_exp (primify_aexp e1, primify_aexp e2)
  | Div_exp (e1, e2) -> Div_exp (primify_aexp e1, primify_aexp e2)
  | Var_exp x -> Var_exp (primify x)
  | Unneg_exp e1 -> Unneg_exp (primify_aexp e1)
  | Havoc_aexp -> e
and
primify_aexp_list lst =
  match lst with
    [] -> []
  | head :: rest ->
    (primify_aexp head) :: (primify_aexp_list rest)

let rec primify_bexp b =
  match b with
    Bool_const bc -> b
  | Eq_exp (e1, e2) -> Eq_exp (primify_aexp e1, primify_aexp e2)
  | Ne_exp (e1, e2) -> Ne_exp (primify_aexp e1, primify_aexp e2)
  | Gt_exp (e1, e2) -> Gt_exp (primify_aexp e1, primify_aexp e2)
  | Lt_exp (e1, e2) -> Lt_exp (primify_aexp e1, primify_aexp e2)
  | Le_exp (e1, e2) -> Le_exp (primify_aexp e1, primify_aexp e2)
  | Ge_exp (e1, e2) -> Ge_exp (primify_aexp e1, primify_aexp e2)
  | And_exp (b1, b2) -> And_exp (primify_bexp b1, primify_bexp b2)
  | Or_exp (b1, b2) -> Or_exp (primify_bexp b1, primify_bexp b2)
  | Not_exp b1 -> Not_exp (primify_bexp b1)
  | Havoc_bexp -> b

let primify_cmd = function
  | Skip -> Skip
  | Assign (x, e) -> Assign(primify x, primify_aexp e)
  | Assert (b) -> Assert (primify_bexp b)
  | Print (e) -> Print (primify_aexp e)
  | Assume (b) -> Assume (primify_bexp b)

let rec nnf = function
  | Bool_const true -> Bool_const true
  | Bool_const false -> Bool_const false
  | Eq_exp (s, t) -> Eq_exp (s, t)
  | Gt_exp (s, t) -> Gt_exp (s, t)
  | Lt_exp (s, t) -> Lt_exp (s, t)
  | Ge_exp (s, t) -> Ge_exp (s, t)
  | Le_exp (s, t) -> Le_exp (s, t)
  | And_exp (phi, psi) -> And_exp (nnf phi, nnf psi)
  | Or_exp (phi, psi) -> Or_exp (nnf phi, nnf psi)
  | Havoc_bexp -> Havoc_bexp
  | Ne_exp (s, t) -> Or_exp (Lt_exp (s, t), Gt_exp (s, t))
  | Not_exp phi -> negate phi
and negate = function
  | Bool_const true -> Bool_const false
  | Bool_const false -> Bool_const true
  | Eq_exp (s, t) -> Or_exp (Lt_exp (s, t), Gt_exp (s, t))
  | Gt_exp (s, t) -> Le_exp (s, t)
  | Lt_exp (s, t) -> Ge_exp (s, t)
  | Ge_exp (s, t) -> Lt_exp (s, t)
  | Le_exp (s, t) -> Gt_exp (s, t)
  | And_exp (phi, psi) -> Or_exp (negate phi, negate psi)
  | Or_exp (phi, psi) -> And_exp (negate phi, negate psi)
  | Havoc_bexp -> Havoc_bexp
  | Ne_exp (s, t) -> Eq_exp (s, t)
  | Not_exp phi -> nnf phi
