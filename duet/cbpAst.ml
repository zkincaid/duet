type binop = And | Or | Xor | Eq | Neq | Implies | Choose
type var =
  { mutable vname : string;
    mutable vid : int }
type 'a open_expr = OTrue | OFalse
                  | OBinop of (binop * 'a * 'a)
                  | OTernary of ('a * 'a * 'a)
                  | ONot of 'a
                  | OVar of var
                  | OPrimeVar of var
                  | OHavoc
type expr = True | False
          | Binop of (binop * expr * expr)
          | Ternary of (expr * expr * expr)
          (*	   | Tilde of expr *)
          | Not of expr
          | Var of var
          | PrimeVar of var
          | Havoc
type stmt = Skip
          (*	    | Dead of (string list) *)
          (*	    | Print of (expr list) *)
          | Goto of (string list)
          | Return of (expr list)
          | Assign of ((var * expr) list * expr option)
          | If of (expr * (lstmt list) * (lstmt list))
          | While of (expr * (lstmt list))
          | Assert of expr
          | Assume of expr
          | Call of (var list * string * expr list)
          | StartThread of string
          | StartThreadGoto of string
          | EndThread
          (*	    | Sync *)
          | AtomicBegin
          | AtomicEnd
and lstmt = int * string list * stmt
type fundec = { name : string;
                returns : int;                (** Number of returns *)
                mutable formals : var list;
                mutable locals : var list; (** Does not include formals *)
                mutable body : lstmt list;
                mutable enforce : expr option; (* ? *)
                mutable abortif : expr option; (* ? *)
                mutable dfs : bool            (* ? *)
              }
type program = { mutable vars : var list;
                 mutable funcs : fundec list }


let rec fold_expr f = function
  | True -> f OTrue
  | False -> f OFalse
  | Binop (op, left, right) ->
    f (OBinop (op, fold_expr f left, fold_expr f right))
  | Ternary (cond, bthen, belse) ->
    f (OTernary (fold_expr f cond, fold_expr f bthen, fold_expr f belse))
  | Not (expr) -> f (ONot (fold_expr f expr))
  | Var x -> f (OVar x)
  | PrimeVar x -> f (OPrimeVar x)
  | Havoc -> f OHavoc

let expr_height =
  let ht = function
    | OTrue | OFalse | OVar _ | OPrimeVar _ | OHavoc -> 1
    | OBinop (_, l, r) -> 1 + (max l r)
    | OTernary (a, b, c) -> 1 + (max a (max b c))
    | ONot e -> 1 + e
  in
  fold_expr ht

let string_of =
  let f = function
    | OTrue -> "1"
    | OFalse -> "0"
    | OBinop (op, left, right) ->
      left ^ (match op with
          | And -> "&&"
          | Or -> "|"
          | Eq  -> "="
          | Neq -> "!="
          | Implies -> "=>"
          | Choose -> "choose"
          | Xor -> "^")
      ^ right
    | ONot expr -> "!" ^ expr
    | OVar v -> v.vname
    | OPrimeVar v -> v.vname ^ "'"
    | OHavoc -> "*"
    | OTernary (cond, bthen, belse) -> cond ^ " ? " ^ bthen ^ " : " ^ belse
  in
  fold_expr f

let label_map = Hashtbl.create 32
let stmt_map = Hashtbl.create 32

let prime_map = Hashtbl.create 32
let max_var = ref 0
let mk_var name =
  let vid = !max_var in
  let var = { vname=name; vid=vid } in
  let prime_var = { vname=name ^ "'"; vid=vid+1 } in
  Hashtbl.add prime_map var.vid prime_var;
  max_var := vid + 2;
  var

let get_primed var =
  try Hashtbl.find prime_map var.vid
  with Not_found -> failwith ("Couldn't find prime for " ^ var.vname)


let mk_lstmt : string list -> stmt -> lstmt =
  let max_id = ref 0 in
  fun labels kind ->
    let id = !max_id in
    let stmt = (id, labels, kind) in
    max_id := id + 1;
    List.iter (fun lbl -> Hashtbl.add label_map lbl stmt) labels;
    Hashtbl.add stmt_map id stmt;
    stmt

let lookup_label lbl =
  try Hashtbl.find label_map lbl
  with Not_found -> failwith ("Label not found: " ^ lbl)
let stmt_of_lstmt (_, _, stmt) = stmt

let transfer_lbls (_, lbls, _) (tgt_id, tgt_lbls, tgt_stmt) =
  let stmt = (tgt_id, lbls @ tgt_lbls, tgt_stmt) in
  List.iter (fun lbl -> Hashtbl.replace label_map lbl stmt) lbls;
  stmt

let set_vars file =
  let lookup_var func name =
    let search = List.find (fun v -> v.vname = name.vname) in
    let res =
      try search func.locals
      with Not_found -> try search func.formals
        with Not_found -> try search file.vars
          with Not_found -> failwith ("Couldn't find variable " ^ name.vname)
    in
    name.vid <- res.vid;
    res
  in
  let f func = function
    | OTrue -> True
    | OFalse -> False
    | OBinop (op, a, b) -> Binop (op, a, b)
    | OTernary (a, b, c) -> Ternary (a, b, c)
    | ONot a -> Not a
    | OVar var -> Var (lookup_var func var)
    | OPrimeVar var -> PrimeVar (get_primed (lookup_var func var))
    | OHavoc -> Havoc
  in
  let set_vars_expr func = fold_expr (f func) in
  let rec set_vars_lstmt func (id, labels, stmt) =
    (id, labels, set_vars_stmt func stmt)
  and set_vars_stmt func = function
    | Return exprs -> Return (List.map (set_vars_expr func) exprs)
    | Assign (asn, constrain) ->
      Assign (List.map
                (fun (x,y) -> (lookup_var func x, set_vars_expr func y))
                asn,
              match constrain with
              | None -> None
              | Some c -> Some (set_vars_expr func c))
    | If (expr, left, right) ->
      If (set_vars_expr func expr,
          List.map (set_vars_lstmt func) left,
          List.map (set_vars_lstmt func) right)
    | While (expr, stmts) ->
      While (set_vars_expr func expr,
             List.map (set_vars_lstmt func) stmts)
    | Assert expr -> Assert (set_vars_expr func expr)
    | Assume expr -> Assume (set_vars_expr func expr)
    | Call (lhs, fn, args) ->
      Call (List.map (lookup_var func) lhs,
            fn,
            List.map (set_vars_expr func) args)
    | x -> x
  in
  let set_vars_func func =
    func.body <- List.map (set_vars_lstmt func) func.body
  in
  List.iter set_vars_func file.funcs;
  file


(*
(* determine whether an expression is a function (i.e., deterministic)
   defined on the current state (i.e., does not include any primed
   variables *)
let expr_current_fun =
  let f = function
    | OTrue -> true
    | OFalse -> true
    | OBinop (Choose, x, y) -> false
    | OBinop (_, x, y) -> x && y
    | OTernary (x, y, z) -> x && y && z
    | ONot x -> x
    | OVar _ -> true
    | OPrimeVar _ -> false
    | OHavoc -> false
  in
    fold_expr f
*)

(* Split an expression into a list of subexpressions.  expr is
   equivalent to the conjunction of the list *)
let rec split_expr = function
  | Binop (And, left, right) ->
    (split_expr left)@(split_expr right)
  | x -> [x]

let substitute f =
  let g = function
    | OTrue -> f True
    | OFalse -> f False
    | OBinop (op, a, b) -> f (Binop (op, a, b))
    | OTernary (a, b, c) -> f (Ternary (a, b, c))
    | ONot a -> f (Not a)
    | OVar v -> f (Var v)
    | OPrimeVar v -> f (PrimeVar v)
    | OHavoc -> f Havoc
  in
  fold_expr g

let simplify = function
  | Assign (xs, Some constrain) ->
    let rec extract_equalities = function
      | Binop (And, a, b) ->
        let (a_expr, a_eq) = extract_equalities a in
        let (b_expr, b_eq) = extract_equalities b in
        (Binop (And, a_expr, b_expr), a_eq@b_eq)
      | Binop (Eq, PrimeVar x, Var y) ->
        if x.vid = (get_primed y).vid then (True, [y])
        else (Binop (Eq, PrimeVar x, Var y), [])
      | Binop (Eq, Var x, PrimeVar y) ->
        if (get_primed x).vid = y.vid then (True, [x])
        else (Binop (Eq, PrimeVar x, Var y), [])
      | x -> (x, [])
    in
    let (constrain, eq) = extract_equalities constrain in
    let asn = List.filter (fun (x, _) -> not (List.mem x eq)) xs in
    let sub = function
      | PrimeVar v -> if List.mem v eq then Var v else PrimeVar v
      | x -> x
    in
    Assign (asn, Some (substitute sub constrain))
  | x -> x
