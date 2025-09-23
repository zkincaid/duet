open Srk


type var = string
type pvar = string
type bvar = int 
type all_var = Variable of var | Pointer of pvar | Block of bvar

type boogie_var = string
type boogie_avar = string

let boogie_var_of_var (v: var) : boogie_var = v
let boogie_var_of_pvar (p: pvar) : boogie_var = p
let boogie_avar_of_bvar (b : bvar) : boogie_avar = "a"^(string_of_int b)
let boogie_length_of_boogie_avar (a : boogie_avar) : boogie_var = "length"^a

let var_name (v : var) : string = "v_"^v
let pvar_name (p : pvar) : string = "p_"^p
let bvar_name (b : bvar) : string = "b_"^string_of_int b

let boogie_var_name (b : boogie_var) : string = String.map (fun c -> if c = '%' then 'v' else (if c = '.' then '_' else c)) b
let boogie_avar_name (a : boogie_avar) : string = a
let boogie_avar_input_name (a : boogie_avar) : string = (boogie_avar_name a)^"_input"
let boogie_avar_local_name (b : boogie_avar) : string = (boogie_avar_name b)^"_local"


let var_to_svar = (Memo.memo (fun v -> Syntax.mk_const Global.srk (Syntax.mk_symbol Global.srk ~name:(boogie_var_name v) `TyInt)))
let pvarblock_to_svar = (Memo.memo (fun p -> Syntax.mk_const Global.srk (Syntax.mk_symbol Global.srk ~name:("block("^(boogie_var_name p)^")") `TyInt)))
let pvaroffset_to_svar = (Memo.memo (fun p -> Syntax.mk_const Global.srk (Syntax.mk_symbol Global.srk ~name:("offset("^(boogie_var_name p)^")") `TyInt)))
let bvar_to_svar (b : bvar) : 'a Syntax.arith_term = Syntax.mk_int Global.srk b

let new_var (name : string) : var = name
let new_pvar (name : string) : pvar = name
let new_bvar (num : int) : bvar = num
let new_avar (name : string) : boogie_avar = name

let prime_var v : var = v^"'"
let prime_pvar v : var = v^"'"

let bvar_of_avar (a : boogie_avar) : bvar = 
  let len = String.length a in
  if len > 1 && String.sub a 0 1 = "a" then
    try int_of_string (String.sub a 1 (len - 1))
    with Failure _ -> failwith ("Invalid boogie array variable: " ^ a)
  else
    failwith ("Invalid boogie array variable: " ^ a)

let generate_new_bvar (ls : boogie_avar list) : bvar = 
  let max_bvar = List.fold_left (fun acc a -> let b = bvar_of_avar a in if b > acc then b else acc) 0 ls in
  let ret = if !Global.max_malloc > max_bvar then !Global.max_malloc else max_bvar in
  Global.max_malloc := ret + 1;
  !Global.max_malloc

module Var = struct 
  type t = BVar of boogie_var | BAVar of boogie_avar
  let pp fmt v = 
    match v with 
    | BVar bv -> Format.fprintf fmt "%s" bv
    | BAVar ba -> Format.fprintf fmt "%s" ba
  let show v = 
    match v with 
    | BVar bv -> bv
    | BAVar ba -> ba
  let typ v = 
    match v with 
    | BVar _ -> `TyInt
    | BAVar _ -> `TyArr
  let compare v1 v2 = 
    match v1, v2 with 
    | BVar bv1, BVar bv2 -> String.compare bv1 bv2
    | BAVar ba1, BAVar ba2 -> String.compare ba1 ba2
    | BVar _, BAVar _ -> -1
    | BAVar _, BVar _ -> 1
  let symbol_of v = 
    match v with 
    | BVar bv -> Syntax.mk_symbol Global.srk ~name:(boogie_var_name bv) `TyInt
    | BAVar ba -> Syntax.mk_symbol Global.srk ~name:(boogie_avar_name ba) `TyArr
  let of_symbol s = 
    let name = Syntax.symbol_name Global.srk s in
    let ty = Syntax.typ_symbol Global.srk s in
    match ty, name with 
    | _, None -> None
    | `TyInt, Some n -> Some (BVar n)
    | `TyArr, Some n -> Some (BAVar n)
    | _, _ -> failwith "Invalid symbol type"
  let is_global _ = true
  let hash v = Hashtbl.hash v
  let equal v1 v2 = (compare v1 v2) = 0
end