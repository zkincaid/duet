open Buddy
open Graph
open Apak
open DatalogCore
open Rename
open Interpreter
open Loop

module StringSet = Set.Make(String)
type polarity = Top | Bottom | Pos | Neg

let join_polarity x y = match x, y with
  | (Bottom, x) | (x, Bottom) -> x
  | (Pos, Pos) -> Pos
  | (Neg, Neg) -> Neg
  | (_, _) -> Top

let negate_polarity = function
  | Bottom -> Bottom
  | Top    -> Top
  | Pos    -> Neg
  | Neg    -> Pos

module Polarity = struct
  type t = polarity
  include Putil.MakeFmt(struct
    type a = t
    let format formatter = function
      | Bottom -> Format.pp_print_string formatter "_|_"
      | Top    -> Format.pp_print_string formatter "T"
      | Pos    -> Format.pp_print_string formatter "+"
      | Neg    -> Format.pp_print_string formatter "-"
  end)
end

module PS = Putil.MonoMap.Make(Putil.PString)(Polarity)

(* Compute the polarity of the body of a rule. *)
let eval_polarity_body body polar_state =
  let get_polarity x =
    try PS.find x polar_state
    with Not_found -> failwith "get_polarity failed"
  in
  let get_literal_polarity = function
    | R (x, _) -> get_polarity x
    | N (x, _) -> negate_polarity (get_polarity x)
  in
  let f polarity rel = join_polarity polarity (get_literal_polarity rel) in
    List.fold_left f Bottom (flatten_body body)

module Fix = Fixpoint.GraphWorklist(K)(K.V)

(* Given a dependence graph and an initial polar state, compute polarities for
   each relation (where the polarity of a relation in the initial polar state
   is Bottom of no tuples have been added or removed from that relation, Pos
   if added but not removed, Neg if removed but not added, and Top otherwise).
   This function is shadowed by another definition of compute_polarities later
   in this file. *)
let compute_polarities_impl g polar_state =
  let polar_state = ref polar_state in
  let set_polarity relation polarity =
    let old_polarity =
      try PS.find relation (!polar_state)
      with Not_found -> Bottom
    in
    let new_polarity = join_polarity old_polarity polarity in
      if old_polarity = new_polarity then false
      else begin
	polar_state := PS.add relation new_polarity (!polar_state);
	true
      end
  in
  let update (head, _, body) =
    set_polarity head (eval_polarity_body body (!polar_state))
  in
    Fix.fix g update;
    !polar_state

let polarities_with_constraints g hard_polar_state =
  let add k v m = match v with
    | Some v -> PS.add k v m
    | None   -> PS.add k Bottom m
  in
  let polar_state = ref (StringMap.fold add hard_polar_state PS.empty) in
  let set_polarity relation polarity =
    match StringMap.find relation hard_polar_state with
      | Some _ -> false
      | None ->
	  let old_polarity =
	    try PS.find relation (!polar_state)
	    with Not_found -> Bottom
	  in
	  let new_polarity =
	    join_polarity old_polarity polarity
	  in
	    if old_polarity = new_polarity then false
	    else begin
	      polar_state := PS.add relation new_polarity (!polar_state);
	      true
	    end
  in
  let update (head, _, body) =
    set_polarity head (eval_polarity_body body (!polar_state))
  in
    Fix.fix g update;
    !polar_state

let relation_of_literal = function
  | R (x, _) | N (x, _) -> x

let revoke_of rel = "revoke$" ^ rel
let add_of rel = "add$" ^ rel

(* Given a rule and a polar state, compute a list of rules for the
   add$/remove$ relations of the head of the rule which are determined by the
   rule.  *)
let get_revoke_rules (hd, param, body) polar_state =
  (* conjoin_revoke and conjoin_add produce the conjunction of a "modified"
     literal and (unmodified) "rest of the body".  "Modified" means the
     revoke$ or add$ version of a relation - which one is produced depends on
     whether the rule body being produced is for a revoke rule or add rule
     (conjoin_revoke vs conjoin_add), whether the literal is positive or
     negative, and the polarity of the relation.  An empty list is produced if
     an appropriate version of the literal does not exist (e.g., if revoke$rel
     is the appropriate modified literal, but rel has positive polarity). *)
  let conjoin_revoke lit rest =
    match (lit, PS.find (relation_of_literal lit) polar_state) with
      | (R (rel, params), Top) | (R (rel, params), Neg) ->
	  [R (revoke_of rel, params)::rest]
      | (N (rel, params), Top) | (N (rel, params), Pos) ->
	  [R (add_of rel, params)::rest]
      | _ -> []
  in
  let conjoin_add lit rest =
    match (lit, PS.find (relation_of_literal lit) polar_state) with
      | (R (rel, params), Top) | (R (rel, params), Pos) ->
	  [R (add_of rel, params)::rest]
      | (N (rel, params), Top) | (N (rel, params), Neg) ->
	  [R (revoke_of rel, params)::rest]
      | _ -> []
  in
  let rewrite_rule head conjoin =
    let f lit (rest, other_rules) =
      (lit::rest, (conjoin lit rest)@(List.map (fun x -> lit::x) other_rules))
    in
      List.map
	(fun body -> (head, param, body))
	(snd (List.fold_right f (flatten_body body) ([], [])))
  in
    match PS.find hd polar_state with
      | Top ->
	  (rewrite_rule (add_of hd) conjoin_add)
	  @(rewrite_rule (revoke_of hd) conjoin_revoke)
      | Pos -> rewrite_rule (add_of hd) conjoin_add
      | Neg -> rewrite_rule (revoke_of hd) conjoin_revoke
      | Bottom -> []

let flip f x y = f y x
let create_subgraph g polar_state =
  let f v =
    PS.find (rule_head v) polar_state != Bottom
  in
  let h = (g,f) in
  let copy = K_sub.fold_edges_e (flip K.add_edge_e) h K.empty in
    K_sub.fold_vertex (flip K.add_vertex) h copy

(* Given an interpreter state, a mapping from relations to added tuples, a
   mapping from relations to removed tuples, and a program, compute a polarity
   for each relation.  This function shadows another definition of
   compute_polarities in this file. *)
let compute_polarities current_state added removed g =
  let init_polarities =
    let add_polarity rel _ polar_state =
      let polarity = match (StringMap.find rel added = bdd_false,
			    StringMap.find rel removed = bdd_false) with
	| (true, true) -> Bottom
	| (false, true) -> Pos
	| (true, false) -> Neg
	| (false, false) -> Top
      in
	PS.add rel polarity polar_state
    in
      State.fold_canonical add_polarity current_state PS.empty
  in 
    compute_polarities_impl g init_polarities

(* Incremental update using the polarity inference algorithm.  Relations of
   polarity Pos or Bottom keep their values from the current state - Top and
   Neg are reset to false *)
(*
let change_tuples_polar current_state initial added removed g =
  let polar_state = compute_polarities current_state added removed g in
  let f rel b =
    let new_bdd =
      match PS.find rel polar_state with
	| Pos -> bdd_or b (PS.find rel added)
	| Bottom -> b
	| Top | Neg ->
	    bdd_diff
	      (bdd_or (PS.find rel initial) (PS.find rel added))
	      (PS.find rel removed)
    in
      (* Get rid of incrementalization info *)
      State.clear current_state rel;
      State.set_value current_state rel new_bdd
  in
    State.iter_value f current_state;
    Log.debug "________POLAR_______";
    Log.debug (Putil.string (pretty_polar_state polar_state));
    Interpreter.eval g current_state
*)

let concrete_polarity old_state new_state =
  let f rel oldv polar_state =
    let newv = State.value new_state rel in
    let polarity =
      if bdd_compare oldv newv = 0 then Bottom
      else if bdd_diff oldv newv = bdd_false then Pos
      else if bdd_diff newv oldv = bdd_false then Neg
      else Top
    in
      PS.add rel polarity polar_state
  in
    State.fold_value f old_state PS.empty

let rec get_heads_wto = function
  | WSimple (head, _, _) -> StringSet.singleton head
  | WLoop xs ->
      List.fold_left StringSet.union StringSet.empty (List.map get_heads_wto xs)

let rec get_heads_wto_list xs = get_heads_wto (WLoop xs)

let change_tuples_polar current_state initial added removed g =
  let old_state = State.copy current_state in
  let wto = simplify_wto (regroup_wto (Order.create g) ([], [])) in
  let polar_state = ref (compute_polarities current_state added removed g) in

  let init_polarities =
    let add_polarity rel _ polar_state =
      let polarity = match (StringMap.find rel added = bdd_false,
			    StringMap.find rel removed = bdd_false) with
	| (true, true) -> Bottom
	| (false, true) -> Pos
	| (true, false) -> Neg
	| (false, false) -> Top
      in
	PS.add rel polarity polar_state
    in
      State.fold_canonical add_polarity current_state PS.empty
  in 
  let add k v m = match v with
    | Bottom -> StringMap.add k None m
    | _ -> StringMap.add k (Some v) m
  in
  let init_polar_state = ref (PS.fold add init_polarities StringMap.empty) in
  let has_reset_value = ref StringSet.empty in
  let reset rel b =
    let new_bdd =
      match PS.find rel (!polar_state) with
	| Pos -> bdd_or b (StringMap.find rel added)
	| Bottom -> b
	| Top | Neg ->
	    bdd_diff
	      (bdd_or (StringMap.find rel initial) (StringMap.find rel added))
	      (StringMap.find rel removed)	    
    in
      Log.debug ("Reset: " ^ rel);
      has_reset_value := StringSet.add rel (!has_reset_value);
      (* Get rid of incrementalization info *)
      State.clear current_state rel;
      State.set_value current_state rel new_bdd
  in
  let eval wto_elem rest graph =
    (* As soon as we encounter a rule with head rel, we need to reset it. *)
    let rec reset_values = function
      | WSimple (head, _, _) ->
	  if not (StringSet.mem head (!has_reset_value))
	  then reset head (State.value current_state head)
      | WLoop xs -> List.iter reset_values xs
    in
    let rec remove_bottom = function
      | WSimple ((head, _, _) as r) ->
	  if PS.find head (!polar_state) = Bottom then None
	  else Some (WSimple r)
      | WLoop xs ->
	  Some (WLoop (List.fold_right
			 (fun x rest -> match x with
			    | Some x -> x::rest
			    | None   -> rest)
			 (List.map remove_bottom xs)
			 []))
    in
    let wto_elem =
      match remove_bottom wto_elem with
	| Some x -> x
	| None -> WLoop [](*failwith "incremental remove_bottom failed"*)
    in
    let remove_predecessors vertex graph =
      K.fold_pred_e (fun e g -> K.remove_edge_e g e) graph vertex graph
    in
    let rec remove_edges wto_elem graph = match wto_elem with
      | WSimple rul -> remove_predecessors rul graph
      | WLoop wto -> List.fold_right remove_edges wto graph
    in
    let heads = get_heads_wto wto_elem in
    let rest_heads = get_heads_wto_list rest in
    let finished_relations = StringSet.diff heads rest_heads in
    let set_concrete_polarity rel =
      let oldv = State.value old_state rel in
      let newv = State.value current_state rel in
      let polarity =
	if bdd_compare oldv newv = 0 then Bottom
	else if bdd_diff oldv newv = bdd_false then Pos
	else if bdd_diff newv oldv = bdd_false then Neg
	else Top
      in
      Format.fprintf
	Log.debug_formatter
	"Set concrete polarity for %s: %a"
	rel
	Polarity.format polarity;
      init_polar_state := StringMap.add rel (Some polarity) (!init_polar_state)
    in
    let graph = remove_edges wto_elem graph in
      Log.debug "-------------------------------------------------------------";
      Log.debug "Evaluating stratum:";
      Log.debug_pp (Loop.format_wto format_rule) [wto_elem];
      reset_values wto_elem;
      W.fix ~wto:(Some [wto_elem]) g (Interpreter.update current_state) None;
      (* set concrete polarities *)
      StringSet.iter set_concrete_polarity finished_relations;
      polar_state := polarities_with_constraints graph (!init_polar_state);
      Log.debug "Polar state after stratum:";
      Log.debug_pp PS.format (!polar_state);
      Log.debug "-------------------------------------------------------------";
      graph
  in
  let rec go graph = function
    | [] -> ()
    | (x::xs) -> go (eval x xs graph) xs
  in
  let ruleless_relations =
    let heads = get_heads_wto_list wto in
    let f x _ set =
      if StringSet.mem x heads then set else StringSet.add x set
    in
      State.fold_canonical f current_state StringSet.empty
  in
  let f head =
    reset head (State.value current_state head)
  in
    StringSet.iter f ruleless_relations;
    go g wto
(*    

  let polar_state = compute_polarities current_state added removed g in
  let f rel b =
    let new_bdd =
      match PS.find rel polar_state with
	| Pos -> bdd_or b (PS.find rel added)
	| Bottom -> b
	| Top | Neg ->
	    bdd_diff
	      (bdd_or (PS.find rel initial) (PS.find rel added))
	      (PS.find rel removed)
    in
      (* Get rid of incrementalization info *)
      State.clear current_state rel;
      State.set_value current_state rel new_bdd
  in
    State.iter_value f current_state;
    Log.debug "________POLAR_______";
    Log.debug (Putil.string (pretty_polar_state polar_state));
    Interpreter.eval g current_state
*)

(* Naive incremental update - throw out the current state and restart the
   computation from the beginning *)
let change_tuples_simple current_state initial added removed g =
  let f rel _ =
    let new_bdd =
      bdd_diff
	(bdd_or (StringMap.find rel initial) (StringMap.find rel added))
	(StringMap.find rel removed)
    in
      (* Get rid of incrementalization info *)
      State.clear current_state rel;
      State.set_value current_state rel new_bdd
  in
    State.iter_value f current_state;
    Interpreter.eval g current_state

(* Incremental update based on over-approximating the tuples than need to be
   removed from each relation, so that we can do something smarter for
   relations with polarity Top and Neg. *)
let change_tuples_revoke current_state initial added removed g =
  let polar_state = compute_polarities current_state added removed g in

  (* Add the add$ and revoke$ relations to the state, along with appropriate
     initial values *)
  let revoke_state =
    let revoke_state = State.copy current_state in
    let add_revoke rel canonical =
      State.new_relation revoke_state (revoke_of rel) canonical;
      State.set_value revoke_state (revoke_of rel) (StringMap.find rel removed)
    in
    let add_add rel canonical =
      State.new_relation revoke_state (add_of rel) canonical;
      State.set_value revoke_state (add_of rel) (StringMap.find rel added)
    in
    let add_revoke_relations rel _ =
      let canonical = State.canonical current_state rel in
	match PS.find rel polar_state with
	  | Top -> begin
	      add_revoke rel canonical;
	      add_add rel canonical
	    end
	  | Pos -> add_add rel canonical
	  | Neg -> add_revoke rel canonical
	  | Bottom -> ()
    in
      State.iter_value add_revoke_relations current_state;
      revoke_state
  in
  let revoke_rules =
    K.fold_vertex (fun v rules -> (get_revoke_rules v polar_state)@rules) g []
  in
  let revoke_rules =
    List.fold_right (fun r lst -> (rebuild r 0)@lst) revoke_rules []
  in
  let revoke_graph = construct_dependence_graph revoke_rules in
  let revoke_value rel = State.value revoke_state (revoke_of rel) in
  let init_value rel =
    bdd_or
      (bdd_diff (StringMap.find rel initial) (StringMap.find rel removed))
      (StringMap.find rel added)
  in

  (* Set the value of relation rel, which has value bdd in the current state,
     by removing those tuples that need to be revoked, and then adding the
     tuples from the inital state. *)
  let set_relation_value rel bdd =
    let new_bdd = 
      match PS.find rel polar_state with
	| Pos -> bdd_or bdd (init_value rel)
	| Bottom -> bdd
	| Neg | Top ->
	    bdd_or (bdd_diff bdd (revoke_value rel)) (init_value rel)
    in
      (* Get rid of incrementalization info *)
      State.clear current_state rel;
      State.set_value current_state rel new_bdd
  in
    Interpreter.eval revoke_graph revoke_state;
    State.iter_value set_relation_value current_state;
    Interpreter.eval g current_state

type strategy = ISSimple | ISRevoke | ISPolar

let incr_strategy = ref ISPolar

(** Incremental update - this function should be the only one accessed outside
    this module. *)
let change_tuples current_state initial added removed g =
  (match !incr_strategy with
     | ISSimple -> change_tuples_simple
     | ISRevoke -> change_tuples_revoke
     | ISPolar -> change_tuples_polar) current_state initial added removed g
