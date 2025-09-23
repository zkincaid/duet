open Symbolicheap
open Variable

module BoAvarSet = Set.Make(struct 
  type t = boogie_avar
  let compare a b = if a < b then -1 else if a > b then 1 else 0
end)

module BoVarSet = Set.Make(struct 
  type t = boogie_var
  let compare a b = if a < b then -1 else if a > b then 1 else 0
end)

type boogie_term = 
  Int of int
  | Var of boogie_var
  | Times of int * boogie_term
  | Sum of boogie_term * boogie_term
  | Read of boogie_avar * boogie_term


type boogie_formula = 
    Leq of boogie_term * boogie_term
  | Eq of boogie_term * boogie_term
  | AEq of boogie_avar * boogie_avar
  | And of boogie_formula * boogie_formula
  | Or of boogie_formula * boogie_formula
  | Not of boogie_formula
  | True

type boogie_instr = 
| Assign of boogie_var * boogie_term 
| AAssign of boogie_avar * boogie_avar 
| AWrite of boogie_avar * boogie_term * boogie_term 
| Assume of boogie_formula 
| Assert of boogie_formula 
| IteAssign of boogie_var * boogie_formula * boogie_term * boogie_term 
| Rotate of (boogie_avar * boogie_avar) list
| Return of boogie_term
| Error

module BGNode = struct 
  type t = int * Llvmutil.LlvmNode.t * symbolicheap * boogie_instr list
  let hash = Hashtbl.hash 

  let compare (a, b, _, _) (c, d, _, _) = if b < d then -1 else if b > d then 1 else if a < c then -1 else if a > c then 1 else 0

  let equal (a, b, _, _) (c, d, _, _) = (b = d) && (a = c)
end

module BGEdge = struct
  type t = boogie_formula option * boogie_instr list option
  let hash = Hashtbl.hash
  let compare a b = if hash a < hash b then -1 else if hash a > hash b then 1 else 0 
  let equal a b = (hash a = hash b)
  let default = None, None
end

module BGraph = Graph.Persistent.Digraph.ConcreteLabeled(BGNode)(BGEdge)


let rec boogie_term_of_pointer_term (p : pointer_term) = 
  match p with 
  | Pointer p -> Var (boogie_var_of_pvar p)
  | PointerSum (p, t) -> Sum (boogie_term_of_pointer_term p, boogie_term_of_int_term t)
and boogie_term_of_int_term (t: int_term) = 
  match t with 
  | Int i -> Int i
  | Var v -> Var (boogie_var_of_var v)
  | Times (i, t) -> Times (i, boogie_term_of_int_term t)
  | Add (t1, t2) -> Sum (boogie_term_of_int_term t1, boogie_term_of_int_term t2)
  | Sub (t1, t2) -> Sum (boogie_term_of_int_term t1, Times (-1, boogie_term_of_int_term t2))
  | Offset p -> boogie_term_of_pointer_term p
  | PSub (p1, p2) -> Sum (boogie_term_of_pointer_term p1, (Times (-1, boogie_term_of_pointer_term p2)))
  

let get_avars (g : BGraph.t) : boogie_avar list = 
  let rec fold_bt t acc = 
    match t with 
    | Int _ -> acc
    | Var _ -> acc
    | Times (_, t) -> fold_bt t acc
    | Sum (t1, t2) -> fold_bt t1 (fold_bt t2 acc)
    | Read (at, t) -> BoAvarSet.add at (fold_bt t acc)
  in 
  BGraph.fold_vertex (fun (_, _, _, ops) acc -> List.fold_left (fun acc op -> 
    match op with 
    | AAssign (a1, a2) -> BoAvarSet.add a1 (BoAvarSet.add a2 acc)
    | AWrite (a, t1, t2) -> BoAvarSet.add a (fold_bt t1 (fold_bt t2 acc))
    | Assign (_, t) -> fold_bt t acc
    | Assume _ -> acc
    | Assert _ -> acc
    | IteAssign (_, _, t1, t2) -> fold_bt t1 (fold_bt t2 acc)
    | Rotate ls -> List.fold_left (fun acc (from, towards) -> BoAvarSet.add from (BoAvarSet.add towards acc)) acc ls
    | Return _ -> acc
    | Error -> acc
    ) acc ops) g BoAvarSet.empty
  |> BoAvarSet.elements

let get_vars (g : BGraph.t) : boogie_var list = 
  let rec fold_bt t acc = 
    match t with 
    | Int _ -> acc
    | Var v -> BoVarSet.add v acc
    | Times (_, t) -> fold_bt t acc
    | Sum (t1, t2) -> fold_bt t1 (fold_bt t2 acc)
    | Read (_, t) -> fold_bt t acc
  in 
  BGraph.fold_vertex (fun (_, _, _, ops) acc -> List.fold_left (fun acc op -> 
    match op with 
    | Assign (v, t) -> fold_bt t (BoVarSet.add v acc)
    | AWrite (_, t1, t2) -> fold_bt t1 (fold_bt t2 acc)
    | AAssign _ -> acc
    | Assume _ -> acc
    | Assert _ -> acc
    | IteAssign (v, _, t1, t2) -> fold_bt t1 (fold_bt t2 (BoVarSet.add v acc))
    | Rotate _ -> acc
    | Return t -> fold_bt t acc
    | Error -> acc
  ) acc ops) g BoVarSet.empty
  |> BoVarSet.elements

let rec bt_text (t : boogie_term) : string = 
  match t with 
  | Int i -> string_of_int i
  | Var v -> boogie_var_name v
  | Times (i, t) -> string_of_int i^" * "^(bt_text t)
  | Sum (t1, t2) -> "("^(bt_text t1)^" + "^(bt_text t2)^")"
  | Read (a, t) ->  (boogie_avar_name a)^"["^(bt_text t)^"]"

  let rec bf_text (f : boogie_formula) : string =
  match f with
  | True -> "true"
  | Leq (t1, t2) -> "("^(bt_text t1)^" <= "^(bt_text t2)^")"
  | Eq (t1, t2) -> "("^(bt_text t1)^" == "^(bt_text t2)^")"
  | AEq (a1, a2) -> "("^(boogie_avar_name a1)^" == "^(boogie_avar_name a2)^")"
  | And (f1, f2) -> "("^(bf_text f1)^" && "^(bf_text f2)^")"
  | Or (f1, f2) -> "("^(bf_text f1)^" || "^(bf_text f2)^")"
  | Not f1 -> "!("^(bf_text f1)^")"

let local_array_uses (g : BGraph.t) : boogie_avar list = 
  (BGraph.fold_vertex (fun (_, _, _, ops) acc -> 
    List.fold_left (fun acc instr -> 
      match instr with 
      | Rotate ls -> List.fold_left (fun acc (from, _) -> BoAvarSet.add from acc) acc ls
      | _ -> acc
      ) acc ops) g BoAvarSet.empty
  |> BoAvarSet.elements) @ 
  (BGraph.fold_edges_e (fun (_, (_, rotation), _) acc -> 
    match rotation with 
    | None -> acc
    | Some instrs -> 
      List.fold_left (fun acc instr -> 
        match instr with 
        | Rotate ls -> List.fold_left (fun acc (from, _) -> BoAvarSet.add from acc) acc ls
        | _ -> acc
      ) acc instrs
    ) g BoAvarSet.empty |> BoAvarSet.elements)

let boogie_instr_text (boogie_instr : boogie_instr) : string = 
  match boogie_instr with 
  | Assign (v, t) -> boogie_var_name v^" := "^(bt_text t)^";\n"
  | AAssign (a1, a2) -> (boogie_avar_name a1) ^" := "^(boogie_avar_name a2)^";\n"
  | AWrite (a, t1, t2) -> (boogie_avar_name a)^"["^(bt_text t1)^"] := "^(bt_text t2)^";\n"
  | Assume f -> "assume "^bf_text f^";\n"
  | Assert f -> "assert "^bf_text f^";\n"
  | IteAssign (v, f, t1, t2) -> 
    let v_text = boogie_var_name v in 
    let t1_text = bt_text t1 in 
    let t2_text = bt_text t2 in 
    let f_text = bf_text f in 
    "if ("^f_text^") {\n"^v_text^" := "^t1_text^";\n} else {\n"^v_text^" := "^t2_text^";\n}\n"
  | Rotate ls -> (
      let local_store = (List.map (fun (from, _) -> (boogie_avar_local_name from)^" := "^(boogie_avar_name from)^";\n") ls |> String.concat "") in 
      let rotate = (List.map (fun (from, towards) -> (boogie_avar_name towards)^" := "^(boogie_avar_local_name from)^";\n") ls |> String.concat "") in 
      local_store ^ rotate
  )
  | Return v -> "retval := "^bt_text v^";\n"
  | Error -> "error;\n"


let code_of_boogie_graph (entry : BGNode.t) (g : BGraph.t) (params : boogie_var list) (array_params : boogie_avar list): string = 
  let returns_statement = "returns ("^(List.fold_left (fun acc a -> (boogie_avar_name a^" : [int]int") :: acc) ["retval : int"] array_params |> String.concat ", ")^")\n" in 
  let params = params @ (List.map boogie_length_of_boogie_avar array_params) in

  let avars = get_avars g |>  List.filter (fun e -> not ( List.mem e array_params))in
  let vars = get_vars g |> List.filter (fun e -> not ( List.mem e params)) in 
  let local_array_uses = local_array_uses g in
  let var_declarations = List.fold_left (fun acc v -> "var "^(boogie_var_name v)^" : int;\n" ^ acc) "" vars 
      ^ (List.fold_left (fun acc a -> 
        "var "^(boogie_avar_name a)^" : [int]int;\n"^
        acc ) "" avars) 
      ^ (List.map (fun a -> "var "^(boogie_avar_local_name a)^" : [int]int;\n") local_array_uses |> String.concat "") in
  
  let (node_name : BGNode.t -> string) = (fun (i, j, _, _) -> "codelabel"^(string_of_int i)^"_"^(Llvmutil.LlvmNode.name j)) in

  let rec go (node : BGNode.t) seen = 
    if List.mem (node_name node) seen then "goto "^(node_name node)^";\n" else 
      let seen = (node_name node) :: seen in 
      let succs = BGraph.succ_e g node in 
      let succ_texts = List.map (fun (_, (cond, rotation), tgt) -> 
        let rotation_text = 
          match rotation with 
          | Some instrs -> String.concat "" (List.map boogie_instr_text instrs)
          | None -> ""
        in 
        match cond with 
        | None -> rotation_text ^ go tgt seen 
        | Some f -> 
          let succ_text = go tgt seen in 
          "if ("^(bf_text f)^") {\n" ^ rotation_text ^ succ_text ^ "}"
      ) succs in 
      let (_, _, _, instrs) = node in
      let node_text = String.concat "" (List.map boogie_instr_text instrs) in 
      (node_name node)^":\n" ^ node_text ^ (String.concat " else " succ_texts) ^ "\n" 
    in
  let array_initialization = (List.fold_left (fun acc a -> 
    boogie_avar_name a^" := "^(boogie_avar_input_name a)^";\n"^acc) "" array_params) in
  let procedure_body = var_declarations^array_initialization^(go entry []) in 
  let parameter_string = String.concat ", " ((List.map (fun p -> (boogie_var_name p) ^ " : int") params) @ 
  (List.fold_left (fun acc a -> ((boogie_avar_input_name a) ^ " : [int]int") :: acc ) [] array_params)) in

  let procedure = "procedure main("^parameter_string^") \n" ^ returns_statement ^ "{\n" ^ procedure_body ^ "}\n" in

  procedure

let generate_new_bvar (graph : BGraph.t) : Variable.bvar = 
  generate_new_bvar (get_avars graph)



let fresh_node_id =
  let c = ref 0 in
  fun () -> incr c; !c

(* Create a new CFG node with a fresh ID and given instructions. 
   Right now I’m using placeholder values for LlvmNode.t and symbolicheap,
   since you’ll replace those with the real ones from your environment. *)
let mk_node instrs =
  let id = fresh_node_id () in
  (id, Llvmutil.dummy, Symbolicheap.true_sheap, instrs)

let rec extract_prefix (instrs : Boogie_ast.stmt list) =
  match instrs with
  | [] -> [], []
  | (Boogie_ast.Assign _ | Boogie_ast.ArrayAssign _ | Boogie_ast.Havoc _ | Boogie_ast.Assume _ | Boogie_ast.Assert _
    | Boogie_ast.Return) as instr :: rest ->
    let prefix, remaining = extract_prefix rest in
    instr :: prefix, remaining
  | _ :: _ -> [], instrs

let rec int_term_of_expr e =
  match e with
  | Boogie_ast.LiteralInt i -> Int i
  | Boogie_ast.LiteralBool b -> Int (if b then 1 else 0)
  | Boogie_ast.LiteralReal _r -> raise (Failure "Real literals not supported in int_term_of_expr")
  | Boogie_ast.Var id -> Var (boogie_var_of_var (new_var id))
  | Boogie_ast.BinaryOp (Boogie_ast.Mul, e1, e2) -> (
      match e1, e2 with
      | Boogie_ast.LiteralInt i, _ -> Times (i, int_term_of_expr e2)
      | _, Boogie_ast.LiteralInt i -> Times (i, int_term_of_expr e1)
      | _ -> raise (Failure "One operand of Times must be a literal integer")
    )
  | Boogie_ast.BinaryOp (Boogie_ast.Add, e1, e2) -> Sum (int_term_of_expr e1, int_term_of_expr e2)
  | Boogie_ast.BinaryOp (Boogie_ast.Sub, e1, e2) -> Sum (int_term_of_expr e1, Times(-1, int_term_of_expr e2))
  | Boogie_ast.UnaryOp (Boogie_ast.Neg, e) -> Times (-1, int_term_of_expr e)
  | Boogie_ast.ArrayAccess (id, index) -> Read (new_avar id, int_term_of_expr index)
  | _ -> raise (Failure "Unsupported expression for int_term_of_expr")

let rec formula_of_expr e = 
  match e with
  | Boogie_ast.BinaryOp (Boogie_ast.Le, e1, e2) -> Leq (int_term_of_expr e1, int_term_of_expr e2)
  | Boogie_ast.BinaryOp (Boogie_ast.Eq, e1, e2) -> Eq (int_term_of_expr e1, int_term_of_expr e2)
  | Boogie_ast.UnaryOp (Boogie_ast.Not, e) -> Not (formula_of_expr e)
  | Boogie_ast.BinaryOp (Boogie_ast.And, e1, e2) -> And (formula_of_expr e1, formula_of_expr e2)
  | Boogie_ast.BinaryOp (Boogie_ast.Or, e1, e2) -> Or (formula_of_expr e1, formula_of_expr e2)
  | _ -> raise (Failure "Unsupported expression for formula_of_expr")

let convert (instr : Boogie_ast.stmt) : boogie_instr = 
  match instr with 
  | Boogie_ast.Assign (id, e) -> Assign (boogie_var_of_var (new_var id), (int_term_of_expr e))
  | Boogie_ast.ArrayAssign (id, index, e) -> AWrite (new_avar id, (int_term_of_expr index), (int_term_of_expr e))
  | Boogie_ast.Havoc id -> Assign (boogie_var_of_var (new_var id), Int 0)  (* Placeholder for havoc *)
  | Boogie_ast.Assume e -> Assume (formula_of_expr e)
  | Boogie_ast.Assert e -> Assert (formula_of_expr e)
  | Boogie_ast.Return -> Return (Int 0)  (* Placeholder for return value *)
  | _ -> Error  (* Placeholder for unsupported instructions *)

module StringMap = Map.Make(String)
let rec add_instrs_to_graph 
  (instrs : Boogie_ast.stmt list) 
  (g : BGraph.t) 
  (label_map : BGNode.t StringMap.t) 
  (goto_edges : (BGNode.t * string) list)
  : BGraph.t * BGNode.t * BGNode.t * (BGNode.t StringMap.t) * ((BGNode.t * string) list) = 
  let prefix, remaining = extract_prefix instrs in
  let prefix_node = mk_node (List.map convert prefix) in
  match remaining with 
  | [] -> BGraph.add_vertex g prefix_node, prefix_node, prefix_node, label_map, goto_edges
  | Boogie_ast.If (cond, then_stmts, else_stmts) :: rest -> 
    (let g', then_entry, then_exit, label_map', goto_edges' = add_instrs_to_graph (then_stmts) g label_map goto_edges in 
    let g'', else_entry, else_exit, label_map'', goto_edges'' = add_instrs_to_graph (else_stmts) g' label_map' goto_edges' in
    let g''', rest_entry, rest_exit, label_map''', goto_edges''' = add_instrs_to_graph rest g'' label_map'' goto_edges'' in
    let cond_formula = formula_of_expr cond in
    let g_final = BGraph.add_edge_e g''' (prefix_node, (Some cond_formula, None), then_entry) in 
    let g_final' = BGraph.add_edge_e g_final (prefix_node, (Some (Not cond_formula), None), else_entry) in 
    let g_final'' = BGraph.add_edge_e g_final' (then_exit, (None, None), rest_entry) in 
    let g_final''' = BGraph.add_edge_e g_final'' (else_exit, (None, None), rest_entry) in 
    g_final''', prefix_node, rest_exit, label_map''', goto_edges''')
  | Boogie_ast.While (cond, body) :: rest -> 
    let g', body_entry, body_exit, label_map', goto_edges' = add_instrs_to_graph body g label_map goto_edges in 
    let g'', rest_entry, rest_exit, label_map'', goto_edges'' = add_instrs_to_graph rest g' label_map' goto_edges' in
    let cond_formula = formula_of_expr cond in
    let g_final = BGraph.add_edge_e g'' (prefix_node, (Some cond_formula, None), body_entry) in
    let g_final' = BGraph.add_edge_e g_final (prefix_node, (Some (Not cond_formula), None), rest_entry) in 
    let g_final'' = BGraph.add_edge_e g_final' (body_exit, (Some cond_formula, None), body_entry) in 
    let g_final''' = BGraph.add_edge_e g_final'' (body_exit, (Some (Not cond_formula), None), rest_entry) in 
    g_final''', prefix_node, rest_exit, label_map'', goto_edges''
  | Boogie_ast.Call (_id, _args) :: _rest -> raise (Failure "Function calls not supported yet")
  | Boogie_ast.Label id :: rest ->
    let g', rest_entry, rest_exit, label_map', goto_edges' = add_instrs_to_graph rest g label_map goto_edges in 
    let g_final = BGraph.add_edge_e g' (prefix_node, (None, None), rest_entry) in
    g_final, prefix_node, rest_exit, (StringMap.add id rest_entry label_map'), goto_edges'
  | Boogie_ast.Goto id :: rest ->
    let g', _rest_entry, rest_exit, label_map', goto_edges' = add_instrs_to_graph rest g label_map goto_edges in
    g', prefix_node, rest_exit, label_map', (prefix_node, id) :: goto_edges'
  | _ -> raise (Failure "Should be part of prefix")




let build_graph (ast : Boogie_ast.program) : BGraph.t = 
  let proc_blocks = List.map (fun proc -> Boogie_ast.body proc) ast.procedures in 
  let g, label_map, goto_edges = List.fold_left (fun (g, label_map, goto_edges) proc_block -> 
    let g', _, _, label_map', goto_edges' = add_instrs_to_graph proc_block g label_map goto_edges in 
    g', label_map', goto_edges'
    ) (BGraph.empty, StringMap.empty, []) proc_blocks in 
  List.fold_left (fun g (from_node, to_label) ->
    match StringMap.find_opt to_label label_map with 
    | Some to_node -> BGraph.add_edge_e g (from_node, (None, None), to_node)
    | None -> raise (Failure ("Undefined label: " ^ to_label))
  ) g goto_edges


open Srk.Syntax
module T = Srk.Transition.Make(Global.Ctx)(Variable.Var)
let rec boogie_term_to_syntax (t : boogie_term) : Global.Ctx.t arith_term = 
  match t with 
  | Int i -> ((mk_int Global.srk i))
  | Var v -> mk_const Global.srk (Variable.Var.symbol_of (BVar v))
  | Times (i, t) -> ((mk_mul Global.srk [mk_int Global.srk i; (boogie_term_to_syntax t)]))
  | Sum (t1, t2) -> mk_add Global.srk [boogie_term_to_syntax t1; boogie_term_to_syntax t2]
  | Read (a, t) -> mk_select Global.srk (mk_const Global.srk (Variable.Var.symbol_of (BAVar a))) (boogie_term_to_syntax t)

let rec boogie_formula_to_syntax (f : boogie_formula) : Global.Ctx.t formula = 
  match f with 
  | True -> mk_true Global.srk 
  | Leq (t1, t2) -> mk_leq Global.srk (boogie_term_to_syntax t1) (boogie_term_to_syntax t2)
  | Eq (t1, t2) -> mk_eq Global.srk (boogie_term_to_syntax t1) (boogie_term_to_syntax t2)
  | AEq (a1, a2) -> mk_eq Global.srk (mk_const Global.srk (Variable.Var.symbol_of (BAVar a1))) (mk_const Global.srk (Variable.Var.symbol_of (BAVar a2)))
  | And (f1, f2) -> mk_and Global.srk [boogie_formula_to_syntax f1; boogie_formula_to_syntax f2]
  | Or (f1, f2) -> mk_or Global.srk [boogie_formula_to_syntax f1; boogie_formula_to_syntax f2]
  | Not f1 -> mk_not Global.srk (boogie_formula_to_syntax f1)

let boogie_instr_to_transition (instr : boogie_instr) : Srk.Transition.Make(Global.Ctx)(Variable.Var).t = 
  let module T = Srk.Transition.Make(Global.Ctx)(Variable.Var) in
  match instr with 
  | Assign (v, t) -> T.arith_assign (BVar v) (boogie_term_to_syntax t)
  | AAssign (a1, a2) -> T.arr_assign (BAVar a1) (mk_const Global.srk (Variable.Var.symbol_of (BAVar a2)))
  | AWrite (a, t1, t2) -> T.arr_assign (BAVar a) (mk_store Global.srk (mk_const Global.srk (Variable.Var.symbol_of (BAVar a))) (boogie_term_to_syntax t1) (boogie_term_to_syntax t2))
  | Assume f -> T.assume (boogie_formula_to_syntax f)
  | Assert f -> T.assume (boogie_formula_to_syntax f) (* Asserts in transition systems? *)
  | IteAssign (v, f, t1, t2) -> T.arith_assign (BVar v) (mk_ite Global.srk (boogie_formula_to_syntax f) (boogie_term_to_syntax t1) (boogie_term_to_syntax t2))
  | Rotate ls -> T.parallel_assign (List.map (fun (from, towards) -> ((Variable.Var.BAVar towards), mk_const Global.srk (Variable.Var.symbol_of (BAVar from)))) ls)
  | Return v -> T.arith_assign (BVar (new_var "retval" |> boogie_var_of_var)) (boogie_term_to_syntax v) (*Is there a canonical return variable?*)
  | _ -> failwith ("Not implemented yet")


  open Srk.TransitionSystem
let graph_to_transition_system (g : BGraph.t) : Srk.TransitionSystem.Make(Global.Ctx)(Variable.Var)(Srk.Transition.Make(Global.Ctx)(Variable.Var)).t =
  let module TS = Srk.TransitionSystem.Make(Global.Ctx)(Variable.Var)(T) in 
  let module WG = Srk.WeightedGraph in 
  
    let label_algebra : T.t label WG.algebra =(
    let add x y = match x, y with
      | Weight x, Weight y -> Weight (T.add x y)
      | _, _ -> invalid_arg "No weight operations for call edges" in
    let mul x y = match x, y with
      | Weight x, Weight y -> Weight (T.mul x y)
      | _, _ -> invalid_arg "No weight operations for call edges" in
    let star = function
      | Weight x -> Weight (T.star x)
      | _ -> invalid_arg "No weight operations for call edges" in
    let zero = Weight T.zero in
    let one = Weight T.one in
    WG.{ add; mul; star; zero; one }) in 

  let empty = WG.empty label_algebra in 

  BGraph.fold_edges_e (fun (v1, (f, i), v2) wg ->
    let (vindex1, _, _, instrs) = v1 in 
    let (vindex2, _, _, _) = v2 in 
    let instrs = match f with 
      | None -> instrs
      | Some f' -> instrs @ [(Assume f')] in 
    let instrs = match i with 
      | None -> instrs
      | Some i' -> instrs @ i' in
    let weight = List.fold_left (fun acc instr -> T.mul acc (boogie_instr_to_transition instr)) T.one instrs in 
    WG.add_edge wg vindex1 (Weight weight) vindex2 
    ) g empty
