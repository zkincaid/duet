open DatalogCore
open Buddy
open Graph
open Apak

module IntMap = Putil.PInt.Map

type restrict_op =
  | OpEq of int * int
  | OpRestrict of int * int

type compiled =
    { exist_after : bdd array;
      univ_after : bdd array;
      relation : string array;
      setops : set_stmt array;
      restrict : restrict_op list array;
      rename : bddpair array;
      negate : bool array;
      head_ops : restrict_op list;
      rename_head : bddpair;
    }

let format_restrict formatter = function
  | OpEq (x, y) -> Format.fprintf formatter "v%d = v%d" x y
  | OpRestrict (x, y) -> Format.fprintf formatter "v%d = %d" x y

type incr =
    { old_values : bdd array;
      old_renamed : bdd array;
      compiled : compiled }

module State : sig
  type t
  val empty : unit -> t
  val new_relation : t -> string -> int list -> unit
  val canonical : t -> string -> int list
  val value : t -> string -> bdd
  val set_value : t -> string -> bdd -> unit
  val fold_canonical : (string -> int list -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_value : (string -> bdd -> 'a -> 'a) -> t -> 'a -> 'a
  val iter_value : (string -> bdd -> unit) -> t -> unit
  val copy : t -> t
  val get_incr : t -> new_rul -> incr option
  val set_incr : t -> new_rul -> incr -> unit
  val clear : t -> string -> unit
  val print : t -> unit
end = struct
  type t =
      { canonical: (string, int list) Hashtbl.t;
	value: (string, bdd) Hashtbl.t;
	incr: (new_rul, incr) Hashtbl.t }
  let empty () =
    { canonical = Hashtbl.create 32;
      value = Hashtbl.create 32;
      incr = Hashtbl.create 32 }
  let new_relation st rel canon =
    if Hashtbl.mem st.canonical rel
    then failwith ("interpreter.new_relation failed: Relation `" ^ rel
		   ^ "' already exists")
    else begin
      Hashtbl.add st.canonical rel canon;
      Hashtbl.add st.value rel bdd_false;
    end

  let canonical st rel =
    try Hashtbl.find st.canonical rel
    with Not_found -> failwith ("Relation `" ^ rel
				^ "' not found in interpreter state!")
  let value st rel =
    try Hashtbl.find st.value rel
    with Not_found -> failwith ("Relation `" ^ rel
				^ "' not found in interpreter state!")

  let set_value st rel bdd =
    try Hashtbl.replace st.value rel bdd;
    with Not_found -> failwith ("Relation `" ^ rel
				^ "' not found in interpreter state!")

  let clear st rel =
    set_value st rel bdd_false;
    Hashtbl.clear st.incr (* todo *)

  let fold_canonical f s init_values =
    Hashtbl.fold f s.canonical init_values

  let fold_value f old_state new_state =
    Hashtbl.fold f old_state.value new_state

  let iter_value f state = Hashtbl.iter f state.value

  let copy x =
    { canonical = Hashtbl.copy x.canonical;
      incr = Hashtbl.copy x.incr;
      value = Hashtbl.copy x.value }

  let get_incr st rul =
    try Some (Hashtbl.find st.incr rul)
    with Not_found -> None
  let set_incr st rul incr =
    try Hashtbl.replace st.incr rul incr
    with Not_found -> Hashtbl.add st.incr rul incr
  let print st =
    let f rel value =
      print_endline rel;
      print_bdd_size value (canonical st rel)
    in
      iter_value f st
end

let compose f g x = f (g (x))

let fdd_relprod v x y = bdd_appex x y 0 (fdd_ithset v)
let bdd_replace x y = if x = bdd_false then x else bdd_replace x y
let bdd_exist x y = if y = bdd_false then x else bdd_exist x y
(* our bdd_relprod v x y = their bdd_relprod x y v

  It's because we are not very smart people. *)
let bdd_relprod v x y =
  if x = bdd_false || y = bdd_false then bdd_false
  else if x = bdd_true then bdd_exist y v
  else if y = bdd_true then bdd_exist x v
  else if v = bdd_false then bdd_and x y
  else bdd_appex x y 0 v
let bdd_not x = if x = bdd_false then bdd_true else bdd_not x

(* Timed bdd operations *)
let bdd_appex w x y z = Log.time "bdd_appex" (bdd_appex w x y) z
let bdd_relprod v x y =
  Log.time "bdd_relprod" (bdd_relprod v x) y
let bdd_or x y = Log.time "bdd_or" (bdd_or x) y
let bdd_and x y = Log.time "bdd_and" (bdd_and x) y
let bdd_exist x y = Log.time "bdd_exist" (bdd_exist x) y
let fdd_equals x y = Log.time "fdd_equals" (fdd_equals x) y
let bdd_restrict x y = Log.time "bdd_restrict" (bdd_restrict x) y
let bdd_replace x y = Log.time "bdd_replace" (bdd_replace x) y
let fdd_setpair x y z = Log.time "fdd_setpair" (fdd_setpair x y) z
let bdd_nodecount = Log.time "bdd_nodecount" bdd_nodecount

let constrained_dimensions bdd =
  let f dim =
    bdd_compare bdd (bdd_exist bdd (fdd_ithset dim)) != 0
  in
    List.filter f (BatList.init (fdd_domainnum ()) (fun x -> x))

let eval_relation_body (name,parameters) canonical bdd = 
  let rename_map =
    let f map formal = function
      | Var actual -> begin
	  try IntMap.add actual (formal::(IntMap.find actual map)) map
	  with Not_found -> IntMap.add actual [formal] map
	end
      | Con _ -> map
    in
      List.fold_left2 f IntMap.empty canonical parameters
  in
  let constrain_eq x bdd var =
    if x = var then bdd
    else fdd_relprod var bdd (fdd_equals x var)
  in
  let constrain_const bdd formal = function
    | Con x -> bdd_restrict bdd (fdd_ithvar formal x)
    | _     -> bdd
  in
  let table = Log.time "bdd_newpair" bdd_newpair () in
  let f actual formals bdd =
    if List.mem actual formals then
      List.fold_left (constrain_eq actual) bdd formals
    else begin
      match formals with
	| (x::xs) ->
	    ignore (fdd_setpair table x actual);
	    List.fold_left (constrain_eq x) bdd xs
	| [] -> failwith "Empty replacement" (* impossible *)
    end
  in
  let bdd = List.fold_left2 constrain_const bdd canonical parameters in
  let bdd = IntMap.fold f rename_map bdd in
    bdd_replace bdd table

let eval_relation_body rel canonical bdd =
  Log.time "eval_relation_body" (eval_relation_body rel canonical) bdd
    
let eval_negation (name, parameters) canonical bdd =
  let b = bdd_not (eval_relation_body (name,parameters) canonical bdd) in
    List.fold_right (fun k b_negated -> match k with
                       | Var (x) -> bdd_and (fdd_domain x) b_negated
                       | Con (x) -> b_negated)
      parameters b

let eval_negation rel canonical bdd =
  Log.time "eval_negation" (eval_negation rel canonical) bdd

let eval_head (name,params) state bd_bdd body_params =
  let eval_bdd v canonical (bddb, unique_vars) =
    match v with
      |  Var (x) -> if (IntMap.mem x unique_vars) then
           let new_bdd =
	     bdd_and (fdd_equals (try IntMap.find x unique_vars with Not_found -> failwith "bdds.ml 45") canonical) bddb
	   in
             (new_bdd, unique_vars)
         else
           (let new_map = IntMap.add x canonical unique_vars in
              (bddb, new_map))
      | Con (x) ->
	  let new_bdd = bdd_and (fdd_ithvar canonical x) bddb in
            (new_bdd, unique_vars)
  in
  let (bddh, rename_map) =
    List.fold_right2 eval_bdd params (State.canonical state name) (bd_bdd, IntMap.empty)
  in
  let bdd_renamed = bddh in
    List.fold_right2 (fun k l bddb -> match k with
                        | Var (x) ->
                            if List.mem x body_params then
                              bddb
                            else bdd_and bddb (fdd_domain x)
                        | Con (x) -> bdd_and (fdd_ithvar l x) bddb) params (State.canonical state name) bdd_renamed

(* Actual -> Formal renaming before we get to the "real" eval_head. *)
let eval_head (name,params) state bd_bdd body_params =
  let formals = State.canonical state name in
  let table = Log.time "bdd_newpair" bdd_newpair () in
  let f actual formal =
    match actual with
      | Var x -> (ignore (fdd_setpair table x formal); Var formal)
      | Con x -> Con x
  in
  let renamed_actuals = List.map2 f params formals in
  let renamed_body_params =
    List.filter (fun x -> not (List.mem x formals)) body_params
  in
  let bdd = bdd_replace bd_bdd table in
    eval_head (name, renamed_actuals) state bdd renamed_body_params

let eval_head rel state bd_bdd body_params =
  Log.time "eval_head" (eval_head rel state bd_bdd) body_params

let eval_literal lit state =
  let k = ns_name lit in
  let canonical = State.canonical state k in
  let bdd = State.value state k in
    match lit with
      | R (k,l) -> eval_relation_body (k,l) canonical bdd
      | N (k,l) -> eval_negation (k,l) canonical bdd

let tuple vars vals =
  let f s var value = bdd_and s (fdd_ithvar var value) in
    if (List.length vars) != (List.length vals)
    then (failwith
        ("Interpreter.tuple: var and value arity does not match ("
        ^(string_of_int (List.length vars))^" versus "
        ^(string_of_int (List.length vals))^" respectively.)"))
    else List.fold_left2 f bdd_true vars vals

(* Construct initial graph where each node is a rule, and each edge which
	 relations in the head of a rule are in the body of another. *)
let construct_dependence_graph new_rules =
  (* Initially, the graph has one vertex for each rule, and no edges *)
  let g =
    List.fold_left (fun g r -> K.add_vertex g r) K.empty new_rules
  in
    (* Find all the rules in the graph g whose head is r and add edges from
       from those rule to the rule with head 'head'. *)
  let add_edges g head r rul =
    let nodes_in_rule = 
      K.fold_vertex (fun ((hd, _, _) as v) lst -> 
		       if hd = r then v::lst else lst)
	g
	[] 
    in
      List.fold_left (fun g r ->  K.add_edge g r rul) g nodes_in_rule
  in
    (* Given a graph and a rule, return a graph with all the vertices and 
       edges of g, plus one edge from head to r for each relation r that 
       appears in the body *)
  let add_rule g rul =
    let (head, _, body) = rul in
    let body_rels = flatten_body body in
      List.fold_left (fun g r ->
			match r with
                          R (x,_) | N (x,_) -> add_edges g head x rul) g body_rels
  in
    (* add all the edges *)
    List.fold_left add_rule g new_rules

let rule_head (x, _, _) = x


(** Compute 3-tuple of:
        - array of existentially quantified variable sets
        - array of universally quantified variable sets
        - array of statements

   such that at each index, the three arrays refer to the same statement.*)
let compile_body body =
  let rec go exist univ = function
    | And (x, Empty) | And (Empty, x) -> go exist univ x
    | And (x, y) -> (* why do we only quantify the latter? -DJ *)
	let (x_exist, x_univ, x_stmt, x_setops) = go bdd_false bdd_false x in
	let (y_exist, y_univ, y_stmt, y_setops) = go exist univ y in
	  (x_exist@y_exist, x_univ@y_univ, x_stmt@y_stmt, x_setops@y_setops)
    | Exist (v, x) -> go (bdd_and (fdd_ithset v) exist) univ x
    | Univ (v, x) -> go exist (bdd_and (fdd_ithset v) univ) x
    | Stmt x -> ([exist], [univ], [x], [])
    | Setop x -> ([exist], [univ], [], [x])
    | Empty -> failwith "compile body"
  in
    match body with
      | Empty -> ([||], [||], [||], [||])
      | _ ->
	  let (exist_after, univ_after, literals, setops) = go bdd_true bdd_true body in
	    (Array.of_list exist_after, Array.of_list univ_after, Array.of_list literals, Array.of_list setops)


let head_ops name params formals =
  let f ops param formal =
    match param with
      | Var x -> if x = formal then ops else OpEq (x, formal)::ops
      | Con x -> (OpRestrict (formal, x))::ops
  in
    List.fold_left2 f [] params formals

let compile_rule (name, params, body) st =
  format_rule Format.std_formatter (name, params, body);
  let (exist_after, univ_after, literals, setops) = compile_body body in
  let negate =
    Array.map (function
		 | N _ -> true
		 | R _ -> false)
      literals
  in
  let relation = Array.map ns_name literals in
  let len = Array.length literals in
  let restrict_ops = Array.make len [] in
  let rename = Array.init len (fun _ -> bdd_newpair ()) in
  let f (name, parameters) i =
    let canonical = State.canonical st name in
    let rename_map =
      let f map formal = function
	| Var actual -> begin
	    try IntMap.add actual (formal::(IntMap.find actual map)) map
	    with Not_found -> IntMap.add actual [formal] map
	  end
	| Con _ -> map
      in
	List.fold_left2 f IntMap.empty canonical parameters
    in
    let constrain_eq x ops var =
      if x = var then ops
      else (OpEq (x, var))::ops
    in
    let constrain_const ops formal = function
      | Con x -> (OpRestrict (formal, x))::ops
      | _     -> ops
    in
    let f actual formals ops =
      if List.mem actual formals then
	List.fold_left (constrain_eq actual) ops formals
      else begin
	match formals with
	  | (x::xs) ->
	      ignore (fdd_setpair rename.(i) x actual);
	      List.fold_left (constrain_eq x) ops xs
	  | [] -> failwith "Empty replacement" (* impossible *)
      end
    in
    let ops = List.fold_left2 constrain_const [] canonical parameters in
      restrict_ops.(i) <- IntMap.fold f rename_map ops;
  in
  let rename_head = bdd_newpair () in

  (* rename actuals & build rename_head *)
  let rec rename_actuals map actuals formals = match actuals, formals with
    | ([], []) -> []
    | ((Var actual)::actuals, formal::formals) ->
	if IntMap.mem actual map then
	  (Var (IntMap.find actual map))::(rename_actuals map actuals formals)
	else begin
	  if formal != actual then
	    ignore (fdd_setpair rename_head actual formal);
	  let map = IntMap.add actual formal map in
	    (Var formal)::(rename_actuals map actuals formals)
	end
    | ((Con x)::actuals, _::formals) ->
	(Con x)::(rename_actuals map actuals formals)
    | (_, _) -> failwith "Interpreter.rename_actuals failed"
  in
  let renamed_actuals =
    rename_actuals IntMap.empty params (State.canonical st name)
  in
    for i = 0 to len - 1 do
      let rel = match literals.(i) with
        R (x, y) | N (x, y) -> (x, y) (* what is this ? *)
      in
	f rel i
    done;
    { exist_after = exist_after;
      univ_after = univ_after;
      setops = setops;
      relation = relation;
      restrict = restrict_ops;
      rename = rename;
      negate = negate;
      head_ops = head_ops name renamed_actuals (State.canonical st name);
      rename_head = rename_head;
    }

let rel_compile st literals =
  Array.map (fun lit -> eval_literal lit st) literals

let rename_literal compiled value i =
  let f bdd op =
    match op with
      | OpEq (x, y) -> fdd_relprod y bdd (fdd_equals x y)
      | OpRestrict (v, x) -> bdd_restrict bdd (fdd_ithvar v x)
  in
  let bdd = List.fold_left f value compiled.restrict.(i) in
  let bdd = bdd_replace bdd compiled.rename.(i) in
    if compiled.negate.(i) then bdd_not bdd
    else bdd

let rename_literal compiled value i =
  Log.time "rename_literal" (rename_literal compiled value) i

let rename_body compiled value =
  Array.init
    (Array.length compiled.relation)
    (fun i -> rename_literal compiled (value i) i)

(* Fetch the fdd block of the arithmetic expression, and the bdd result
   
   bdd_from_fdd : fdd -> boolean -> bdd
     Used for computing the bdd for an fdd (possibly negated)
     For example, compute the bdd of "x in that_fdd, possibly negated"
     or just straight up the bdd of "that_fdd, possibly negated" *)
let rec eval_containment_expr e bdd_from_fdd = match e with
  | Atom x -> bdd_from_fdd true x
  | NegatedAtom x -> bdd_from_fdd false x
  | BinaryOp (op, a, b) ->
    let a = eval_containment_expr a bdd_from_fdd in
    let b = eval_containment_expr b bdd_from_fdd in
    match op with
    | OperatorUnion -> bdd_or a b
    | OperatorIntersection -> bdd_and a b

let rec eval_setrel_expr_bit lhs_vars rhs_vars bdd_from_bits i =
  let l_var = lhs_vars.(i) in
  match rhs_vars with
  | Atom x -> bdd_from_bits true l_var x.(i)
  | NegatedAtom x -> bdd_from_bits false l_var x.(i)
  | BinaryOp (op, a, b) ->
    let a = eval_setrel_expr_bit lhs_vars a bdd_from_bits i in
    let b = eval_setrel_expr_bit lhs_vars b bdd_from_bits i in
    match op with
    | OperatorUnion ->
        (* Two cases:
            * One of them has l_var=1
            * both of them have l_var = 0
           Nothing else is accepted. *)
        bdd_or (bdd_and (bdd_ithvar l_var) (bdd_or a b))
               (bdd_and (bdd_nithvar l_var) (bdd_and a b)) 
    | OperatorIntersection ->
        (* Similar to OperatorUnion (but backwards)*)
        bdd_or (bdd_and (bdd_ithvar l_var) (bdd_and a b))
               (bdd_and (bdd_nithvar l_var) (bdd_or a b))

(* Temporary stopgap until constants can work *)
let fdd_of_eq_var = function
    | Con x -> failwith "No constants here (yet)"
    | Var x -> x

let eval_setrel_expr lhs rhs bdd_from_bits =
  let lhs = fdd_of_eq_var lhs in
  let start_bdd = ref bdd_true in
  let lhs_vars = (fdd_vars lhs) in
  let rhs_treevars = arith_expr_map (compose fdd_vars fdd_of_eq_var) rhs in begin
  let runbit = eval_setrel_expr_bit lhs_vars rhs_treevars bdd_from_bits in
    for i = 0 to Array.length lhs_vars - 1 do
      start_bdd := bdd_and !start_bdd (runbit i)
    done;
    !start_bdd
  end

(* Define a bdd for any set (in fdd_set) that contains/doesn't contain i

  It checks for containment if positive is true, noncontainment otherwise.*)
let set_for_i positive fdd_set i =
  let set_var = (Array.get (fdd_vars fdd_set) i) in
  let bdd_var = (if positive then bdd_ithvar else bdd_nithvar) in
    bdd_var set_var

(*let rec set_for_exp create_bdd_callback fdd_exp =
  match fdd_exp with
  | Atom (Var x) -> (create_bdd_callback x)
  | Atom (Con _) -> failwith "No constants allowed in `in` statements on the RHS"
  | UnaryOp (op, x) -> begin
    let x_bdd = (set_for_exp create_bdd_callback fdd_exp) in
    match op with
    | OperatorComplement -> bdd_not x_bdd
    end *)

(* Create a bdd for "this is (not) in the set represented by `fdd`" *)
let create_in_fdd fdd_e fdd_set positive = begin
  let containment_bdd = ref bdd_false in
  for e_val = 0 to (fdd_domainsize fdd_e) - 1 do
    let term = (bdd_and (fdd_ithvar fdd_e e_val) (set_for_i positive fdd_set e_val)) in
      containment_bdd := (bdd_or !containment_bdd term)
  done;
  !containment_bdd
  end

let create_in_bdd (positive, var_e, expr) =
  match var_e with
  | Con _ -> failwith "No constants allowed in `in` statements on the LHS"
  | Var fdd_e ->
    let expr_fddtree = arith_expr_map fdd_of_eq_var expr in
    eval_containment_expr
        expr_fddtree
        (fun pos fdd -> create_in_fdd fdd_e fdd (pos = positive))
        (* work out the cases for pos = positive ;) *)

(* Because the stdlib is terrible*)
let larray_map2 f a b = List.map2 f (Array.to_list a) (Array.to_list b)

(* For every bit `b_x` and `b_y` in fdd_x/fdd_y (resp.), constrain somehow.
   Join the constraints as any (if bdd_join is `or` and bdd_base is false) or
   all (if bdd_join is `and` and bdd_base is true)
   of the bits satisfy the constraint.

   does that make sense? :S *)
let fdd_constrain_bits_withjoin bdd_join bdd_base constrain fdd_x fdd_y =
  let constraining_bdds = larray_map2 constrain (fdd_vars fdd_x) (fdd_vars fdd_y)
  in
    List.fold_left bdd_join bdd_base constraining_bdds

let fdd_constrain_allbits = fdd_constrain_bits_withjoin bdd_and bdd_true
let fdd_constrain_anybits = fdd_constrain_bits_withjoin bdd_or bdd_false

(* Constrain bits so that they are <= *)
let constrain_lte x_bit y_bit =
  bdd_or
    (bdd_nithvar x_bit)
    (bdd_ithvar y_bit)

(* constrain bits so they are < *)
let constrain_lt x_bit y_bit =
  bdd_and
    (bdd_nithvar x_bit)
    (bdd_ithvar y_bit)

(* Haskell! *)
let flip f a b = f b a
let constrain_gte = flip constrain_lte
let constrain_gt = flip constrain_lt

let constrain_eq x_bit y_bit =
  bdd_or
    (bdd_and
      (bdd_ithvar x_bit)
      (bdd_ithvar y_bit))
    (bdd_and
      (bdd_nithvar x_bit)
      (bdd_nithvar y_bit))

let constrain_neq x_bit y_bit =
  bdd_or
    (bdd_and
      (bdd_ithvar x_bit)
      (bdd_nithvar y_bit))
    (bdd_and
      (bdd_nithvar x_bit)
      (bdd_ithvar y_bit))

let create_setrel_bdd (rel, lhs, rhs) =
  let eval = eval_setrel_expr lhs rhs in
  match rel with
  | SetSubset -> eval (function true -> constrain_lte | false -> constrain_gte)
  | SetEq -> eval (function true -> constrain_eq | false -> constrain_neq)
  | SetSuperset -> eval (function true -> constrain_gte | false -> constrain_lte)

let eval_compiled compiled value bdd =
  let len = Array.length compiled.relation in
  let rec go i bdd =
    if i >= len || bdd = bdd_false then bdd else begin
      let other_bdd = (value i) in
      let bdd =
	bdd_relprod compiled.exist_after.(i) bdd other_bdd
      in
      let bdd = (* no longer need to do the conjunction, just quantify  *)
        bdd_forall bdd compiled.univ_after.(i)
      in
	go (i+1) bdd
    end
  in
  let f bdd op =
    match op with
      | OpEq (x, y) -> bdd_and bdd (fdd_equals x y)
      | OpRestrict (v, x) -> bdd_and bdd (fdd_ithvar v x)
  in
  let bdd = Log.time "replace compiled" (bdd_replace (go 0 bdd)) compiled.rename_head in
  let containment_checks, setrel_checks = Array.fold_left
      (fun (conts, setrels) next -> match next with
       | StmtIn a -> (a::conts, setrels)
       | StmtSetRelation a -> (conts, a::setrels))
      ([], [])
      compiled.setops
  in
  let containment_bdds = List.map create_in_bdd containment_checks in
  let post_containment_result = List.fold_left bdd_and bdd containment_bdds in
  let is_bdds = List.map create_setrel_bdd setrel_checks in
  let post_is_result = List.fold_left bdd_and post_containment_result is_bdds in
  let result = List.fold_left f post_is_result compiled.head_ops in
    result

let eval_compiled compiled value bdd =
  Log.time "eval_compiled" (eval_compiled compiled value) bdd

let update_nonincremental ((head, params, body) as r) st =
  let compiled = compile_rule r st in
  let body_values = Array.map (State.value st) compiled.relation in
  let body_renamed = rename_body compiled (Array.get body_values) in
  let newv = eval_compiled compiled (Array.get body_renamed) bdd_true in
  let oldv = State.value st head in
  let newv = bdd_or oldv newv in
    State.set_value st head newv;
    if Array.length body_values >= 1 then begin
      State.set_incr st r { old_values = body_values;
			    old_renamed = body_renamed;
			    compiled = compiled }
    end;
    if !Log.debug_mode
    then print_bdd_size newv (State.canonical st head);
    oldv != newv

let update_incremental ((head, params, body) as r) incr st =
  if body = Empty then update_nonincremental r st else
    let old_body = incr.old_values in
    let compiled = incr.compiled in
    let body_values = Array.map (State.value st) compiled.relation in
    let len = Array.length body_values in
      
    let body_values = Array.map (State.value st) compiled.relation in

    let deltas =
      Array.init len (fun i ->
			if compiled.negate.(i)
			  || body_values.(i) = old_body.(i)
			then bdd_false
			else bdd_diff body_values.(i) old_body.(i))
    in
    let renamed_deltas =
      Array.init len
	(fun i ->
	   if compiled.negate.(i) || deltas.(i) = bdd_false then bdd_false
	   else rename_literal compiled deltas.(i) i)
    in
      let need_body = (* true if we need *all* bodies *)
      let rec go i c =
	if i >= len then false
	else let changed = renamed_deltas.(i) != bdd_false in
	  (c && changed || go (i+1) (c || changed))
      in
	go 0 false
    in
    let renamed_body =
      Array.init len (fun i ->
			if compiled.negate.(i) then incr.old_renamed.(i)
			else if need_body || renamed_deltas.(i) = bdd_false
			then (if incr.old_renamed.(i) = bdd_false
			      then rename_literal compiled body_values.(i) i
			      else bdd_or renamed_deltas.(i) incr.old_renamed.(i))
			else bdd_false)
    in
    let eval_body i =
      let value j = if i = j then bdd_true else renamed_body.(j) in
	eval_compiled compiled value renamed_deltas.(i)
    in
    let rec go i bdd =
      if i >= len then bdd
      else go (i + 1) (if compiled.negate.(i) || renamed_deltas.(i) = bdd_false
		       then bdd
		       else bdd_or bdd (eval_body i))
    in
    let oldv = State.value st head in
    let newv = go 0 oldv in
      State.set_value st head newv;
      State.set_incr st r {incr with
			     old_values = body_values;
			     old_renamed = renamed_body};
      if !Log.debug_mode
      then print_bdd_size newv (State.canonical st head);
      oldv != newv

let update st r =
  match State.get_incr st r with
    | Some old ->
	Log.log ~level:Log.fix "Evaluating rule (inc)";
	Log.log_pp ~level:Log.fix format_rule r;
	update_incremental r old st
    | None ->
	Log.log ~level:Log.fix "Evaluating rule";
	Log.log_pp ~level:Log.fix format_rule r;
	update_nonincremental r st


let is_recursive (head, _, body) =
  List.exists
    (function R (r, _) | N (r, _) -> r = head)
    (flatten_body body)

module W = Fixpoint.Wto(K)
module Order = Loop.Wto(K)

(* Tighten inner loops *)
let rec regroup_wto xs (group, rest) =
  let end_group group =
    let group = List.rev group in
    let (recursive, nonrecursive) = List.partition is_recursive group in
    let nonrecursive = List.map (fun x -> Loop.WSimple x) nonrecursive in
    let recursive = List.map (fun x -> Loop.WSimple x) recursive in
      if recursive = [] then nonrecursive
      else (Loop.WLoop recursive)::nonrecursive
  in
    match xs with
      | ((Loop.WLoop loop)::xs) ->
	  regroup_wto xs
	    ([],
	     rest@(end_group group)@[Loop.WLoop (regroup_wto loop ([], []))])
      | ((Loop.WSimple ((h,_,_) as x))::xs) ->
	  if group = [] then regroup_wto xs ([x], rest)
	  else begin
	    let (group_head, _, _) = List.hd group in
	      if h = group_head then regroup_wto xs (x::group, rest)
	      else regroup_wto xs ([x], rest@(end_group group))
	  end
      | [] -> rest@(end_group group)

(* Get rid of loops of the form WLoop [WLoop _] *)
let simplify_wto wto =
  let rec go = function
    | Loop.WSimple x -> Loop.WSimple x
    | Loop.WLoop [Loop.WLoop x] -> go (Loop.WLoop x)
    | Loop.WLoop x -> Loop.WLoop (List.map go x)
  in
    List.map go wto

let eval graph state =
  let wto = simplify_wto (regroup_wto (Order.create graph) ([], [])) in
    W.fix ~wto:(Some wto) graph (update state) None
