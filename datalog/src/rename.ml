open Apak
open Buddy
open Graph
open DatalogCore
open DisjointSet

type rep = Undef | Def of string
module HT = Hashtbl
module M = struct
    type t = string
    let compare = Pervasives.compare
    let equal = Pervasives.(=)
    let hash = Hashtbl.hash
end
module DS = DisjointSet.Make(M)

module IntSet = Putil.PInt.Set

let unrep = function
  | Def p -> p
  | Undef -> failwith "unrep failed!"

let print_renaming body =
  List.fold_right (fun k s -> match k with
                     | R (x,_) -> x^s
                     | N (x,_) -> x^" "^s) body ""

(* Get an fdd variable for a (domain,integer) pair *)
let get_dvar domain i di =
  try HT.find di.dvars (domain, i)
  with Not_found ->
    let a = dom_size domain di in
    let var = fdd_extdomain a  in
      HT.add di.dvars (domain, i) var;
      var

(* Local domain information *)
type ldi = { count : (string, int) HT.t;
	     vars : (string, int) HT.t;
	     di : di }

(* Retrieve the next available fdd variable for a particular domain *)
let new_var domain ldi =
  let i = try HT.find ldi.count domain with Not_found -> failwith "renaming.ml 33" in
  let var = get_dvar domain i ldi.di in
    HT.replace ldi.count domain (i + 1);
    var

(* Retrieve the fdd variable corresponding to a variable *)
let get_var var domain ldi =
  try HT.find ldi.vars var
  with Not_found ->
    let v = new_var domain ldi in
      HT.add ldi.vars var v;
      v

(* Just what it seems *)
let tryfind ht v =
  try Some (Hashtbl.find ht v)
  with Not_found -> None

let find_relat r p =
   snd (try List.find (fun (a,_) -> a = r) p with Not_found -> failwith ("renaming.ml find_relat."^r))

(* create a new local domain information structure *)
let new_ldi di =
  let count = HT.create 32 in
    HT.iter (fun d _ -> HT.add count d 0) di.size;
    { count = count; di = di; vars = HT.create 32 }

let construct_equalities_disjoint_set eqs =
  let ds = DS.create 1 in
    List.iter 
        (fun (x,y) ->
            ignore(DS.union
                (DS.find ds (x))
                (DS.find ds (y))))
        eqs;
    ds

let rec rename_arith_expr renamed_param_ht haystack_exp =
  let recurse x = rename_arith_expr renamed_param_ht x in
  match haystack_exp with
  | Atom x -> Atom (Hashtbl.find renamed_param_ht x)
  | NegatedAtom x -> NegatedAtom (Hashtbl.find renamed_param_ht x)
  | BinaryOp (op, x, y) -> BinaryOp (op, recurse x, recurse y)

let rename_rule rul di relations domainpsets =
  (* create a new local domain variable hash table *)
  let new_ldi = new_ldi di in
  let (head_name, head_params, forall_params, body) = rul in
    (* separate the relations and equalities in the body
       of the rule. *)
  let (rels, eqs, ins, setrels) =
    List.fold_left (fun (rels,eqs,ins,setrels) k ->
                      match k with
                        | Rel _ | Neg _ -> (k::rels, eqs, ins, setrels)
                        | EQ (x, y) -> (rels, (x, y)::eqs, ins, setrels)
                        | In (x, y) -> (rels, eqs, (true, x, y)::ins, setrels)
                        | Nin (x, y) -> (rels, eqs, (false, x, y)::ins, setrels)
                        | SetRelation a -> (rels, eqs, ins, a::setrels))
      ([],[],[],[]) body in
  let params_in_eqs =
    List.fold_left (fun lst (x,y) -> 
                      if (is_int x) && (is_int y) then lst
                      else 
                        (if (is_int x) then y::lst
                         else x::(y::lst))) [] eqs in
  let g =  
    let disjoint_sets = construct_equalities_disjoint_set eqs in
    let f x rep =
      match rep with
        | Undef -> Def x
        | Def y -> 
	    if ((is_int x) && (is_int y)) then
              if (int_of_string x) = (int_of_string y) then Def x
              else raise NotEqualConstants
	    else
              (if (is_int x) then Def x
               else
		 (if (List.mem x head_params) then
		    if (is_int y) then Def y
		    else Def x
		  else
		    Def y))
    in  
      DS.reverse_map disjoint_sets Undef f
  in
  let renamed_param_ht = match rul with (_,args,_,_) -> Hashtbl.create (List.length args) in
  let var_domain_ht = match rul with (_,args,_,_) -> Hashtbl.create (List.length args) in
  let rename_params relname relargs =
    let rename_param var_expr domain = begin
      Hashtbl.add var_domain_ht var_expr domain;
      if (is_int var_expr)
        then (Con (int_of_string var_expr))
      else if var_expr = "_"
        then (Var (new_var domain new_ldi))
      else if (List.mem var_expr params_in_eqs)
        then let p = unrep (g var_expr) in
        if (is_int p)
            then (Con (int_of_string p))
            else (Var (get_var p domain new_ldi))
      else
        (Var (get_var var_expr domain new_ldi))
      end
    in
    let rename_record_param var_expr domain = 
      let renamed = rename_param var_expr domain in begin
        Hashtbl.add renamed_param_ht var_expr renamed;
        renamed
      end
    in
      List.map2 rename_record_param relargs (find_relat relname relations)
  in
  let rename_relations rels = List.fold_left 
        (fun lst r -> match r with
                      | EQ _ -> failwith "EQ encountered in rename_relations"
                      | In _ -> failwith "In encountered in rename_relations"
                      | Nin _ -> failwith "Nin encountered in rename_relations"
                      | SetRelation _ -> failwith "Set relation encountered in rename_relations"
                      (* copypasta here. Indicates to me that maybe negation
                         should be stored as a flag instead ... *)
                      | Rel (x,y) ->
                            let renamed_params = (rename_params x y) in
                                R (x, renamed_params)::lst
                      | Neg (x,y) ->
                            let renamed_params = (rename_params x y) in
                                N (x, renamed_params)::lst)
        []
        rels
  in
  let rename_ops ops = List.map
        (fun (modifier, lhs, rhs) ->
          let renamed_lhs = Hashtbl.find renamed_param_ht lhs in
          match renamed_lhs with
          | Con _ -> failwith "Expression values cannot be constants"
          | Var _ ->
          let renamed_rhs= rename_arith_expr renamed_param_ht rhs in 
            (modifier, renamed_lhs, renamed_rhs))
        ops
  in
  let renamed_rels = rename_relations (List.rev rels) in
  let renamed_ins = List.map (fun x -> StmtIn x) (rename_ops ins) in
  let renamed_setrels = List.map
    (fun setrel_tuple -> StmtSetRelation setrel_tuple)
    (rename_ops setrels)
  in
  let renamed_ops = renamed_ins @ renamed_setrels in
  let forall_vars = List.map
    (fun k -> match (Hashtbl.find renamed_param_ht k) with
        | Con _ -> failwith "forall_vars: Can't universally quantify constants"
        | Var x -> x)
    (List.filter (Hashtbl.mem renamed_param_ht) forall_params)
  in 
  let hdparameters = rename_params head_name head_params in
    (head_name, hdparameters, renamed_rels, renamed_ops, forall_vars)
(*------------------------------------------------------------------*)
(* Find the pair of the pair_lst whose second element is the smallest one. Return only the first element *)
let find_minimum pair_lst =
  let (v,n) =
    List.fold_left (fun (v,n) (k,l) -> if (l < n) then (k,l) else (v,n)) (List.hd pair_lst) pair_lst
  in
    v

let only_in_body (_, head_params, bd) =
  let fold_vars f =
    List.fold_left (fun a k -> match k with
		      | Var x -> f a x
		      | Con _ -> a)
  in
  let head_vars = fold_vars (fun xs x -> x::xs) [] head_params in
  let in_head x = List.mem x head_vars in
  let add_exist_vars vars k =
    let params =
      match k with R (_, params) | N (_, params) -> params
    in
      fold_vars
	(fun vars x -> if in_head x then vars else IntSet.add x vars)
	vars
	params
  in
    IntSet.elements (List.fold_left add_exist_vars IntSet.empty bd)

let in_relation v rel =
    match rel with R (_,y) | N (_, y) -> List.mem (Var v) y

let rec in_arith_expr v exp =
  match exp with
  | Atom x | NegatedAtom x -> (Var v) = x
  | BinaryOp (_, x, y) -> in_arith_expr v x || in_arith_expr v y

let rec in_expression v exp =
  match exp with
    | And (x,y) -> (in_expression v x) || (in_expression v y)
    | Exist (_,y) | Univ (_,y) -> (in_expression v y)
    | Stmt x -> in_relation v x
    | Setop (StmtIn (_, var, e) | StmtSetRelation (_, var, e)) -> (Var v) = var || in_arith_expr v e
    | Empty -> false

(* Return the number of relations that the variable v appears in*)
let get_num_rels v bd = 
  List.fold_left (fun n rel -> if (in_relation v rel) then n+1
                  else n) 0 bd

let opt_and x y =
  match (x,y) with
    | (Empty,k) -> k
    | (k, Empty) -> k
    | (k,l)-> And (k,l)

(* From an ae, create a tuple where:
        fst contains `var` (an existentially quantified variable)
        snd doesn't.
   or something like that. -DJ*)
let rec creat_exist_struct var exp =
  match exp with
    | And (x,y) -> 
        let (x0,x1) = creat_exist_struct var x in
        let (y0,y1) = creat_exist_struct var y in
            (opt_and x0 y0, opt_and x1 y1)
    | Exist _ | Univ _ | Stmt _ | Setop _ ->
      if (in_expression var exp)
        then (exp, Empty)
        else (Empty, exp)
    | Empty -> (Empty, Empty)

let creat_and_struct stmts setops =
  let stmts = match stmts with
    | [] -> Empty
    | (r::rs) -> List.fold_left (fun bd r -> And (Stmt r, bd)) (Stmt r) rs
  in
  let setops = match setops with
    | [] -> Empty
    | (r::rs) -> List.fold_left (fun bd r -> And (Setop r, bd)) (Setop r) rs
  in match (stmts, setops) with
    | (Empty, Empty) -> Empty
    | (a, Empty) -> a
    | (Empty, b) -> b
    | (a, b) -> And (a, b)

(* Go through all the existentially quantified variables --
   from most to least commonly used -- and create `Exist` nodes for them. *)
let rec exist_vars pair_lst exp =
  if (List.length pair_lst == 0) then
    exp
  else (
    let current_var = find_minimum pair_lst in
    let (new_exp0, new_exp1) = creat_exist_struct current_var exp in
    let new_pair_lst = List.remove_assoc current_var pair_lst in
      match (new_exp0, new_exp1) with
        | (Empty, x) -> exist_vars new_pair_lst x
        | (x, Empty) -> Exist (current_var, exist_vars new_pair_lst x)
        | (x,y) -> exist_vars new_pair_lst (And (Exist (current_var,x),y)) )
(* -------------------------------------------- *)
(* Return true if the rule (hd,bd) is recursive, and false otherwise. *)
(* This is also defined, in a different form, in interpreter.ml . What's up? *)
let is_recursive (head,_,bd) =
    List.mem head (List.map ns_name bd)

let build_and_exist_structure rul di relations domainpsets num_of_helpers =
  let renamed_rul = rename_rule rul di relations domainpsets in
  let (hd, params, body, setops, forall_vars) = renamed_rul in
    if List.length body = 0 then [(hd, params, Empty)]
    else begin
      let free_variables = only_in_body (hd, params, body) in
      let body = creat_and_struct body setops in
      let quantify var body = 
        if (List.mem var forall_vars) (* This is quadratic time, but, eh. *)
            then Univ (var, body)
            else Exist (var, body)
      in
	[(hd, params, List.fold_right quantify free_variables body)]
    end


(* --------------------------------------------------------------- *)
let rename_relation rel di =
  let new_ldi = new_ldi di in
    let fdd_parameters =
      List.fold_left (fun lst t -> (new_var t new_ldi)::lst)
                      [] (snd rel)
    in
      (fst rel, List.rev (fdd_parameters))
(*let rename_relation rel di =
  let new_ldi = new_ldi di in
    let fdd_parameters = 
      List.fold_right (fun t lst -> (new_var t new_ldi)::lst)
                      (snd rel) []
    in
      (fst rel, fdd_parameters)*)


let rec print_rule bd =
  match bd with
    | Empty -> ""
    | And (x, y) -> (" and (" ^ (print_rule x) ^ ") (" ^ (print_rule y) ^ ")")
    | Exist (x, y) -> (" exist (" ^ (print_rule y) ^ " )")
    | Univ (x, y) -> (" forall (" ^ (print_rule y) ^ " )")
    | Stmt x -> (match x with R (k,_) | N (k,_) -> k)
    | Setop x -> (string_of_set_stmt x)

let print_rule_body bd = 
  print_endline (print_rule bd)
(* ------------------------------------------------- *)
let rebuild renamed_rul num_of_helpers =
  let (hd, params, body) = renamed_rul in
    (* the variables that appear only in the body of the rule *)
  let to_exist = only_in_body renamed_rul
  in
    (* Create a list of pairs where the first element in each pair will be a
       variable from the to_exist list, and the second element will be the
       number of relations that variable appears in the body *)
  let pair_lst = 
    List.fold_left (fun lst v -> (v, get_num_rels v body)::lst) [] to_exist
  in
    if (List.length body == 0) then [(hd,params,Empty)]
    else (
        let and_struct = creat_and_struct body [] in (* FIXME NOT AT ALL RIGHT *)
	  [(hd, params, exist_vars pair_lst and_struct)])

