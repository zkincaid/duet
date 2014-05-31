open Loop

(** Compute a fixpoint over a weak topological order *)
let fix_wto wto update =
  let evaluations = ref 0 in
  let rec fix = function
    | WSimple x -> (incr evaluations; update x)
    | WLoop xs ->
      let f changed x = fix x || changed in
      let rec loop changed =
	if List.fold_left f false xs
	then loop true
	else changed
      in
      loop false
  in
  List.iter (fun elt -> ignore (fix elt)) wto;
  Log.logf ~level:Log.fix "Evaluations: %d" (!evaluations)

module type G = sig
  include Loop.G
  module E : Graph.Sig.EDGE with type vertex = V.t
  val iter_edges_e : (E.t -> unit) -> t -> unit
end
module Wto (G : G) = struct
  module Order = Wto(G)
  module VSet = Set.Make(G.V)

  let vertices g = G.fold_vertex VSet.add g VSet.empty

  let fix graph ?wto:(wto=None) ?init:(vs=vertices graph) update wide_update =
    let evaluations = ref 0 in
    let (update, wto) = match wto, wide_update with
      | (None, Some widen) ->
	let (wto, is_widening) = Order.create_widening graph in
	let update v = if is_widening v then widen v else update v in
	(update, wto)
      | (None, None) -> (update, Order.create graph)
      | (Some wto, Some widen) ->
	let (_, is_widening) = Order.create_widening graph in
 	let update v = if is_widening v then widen v else update v in
 	(update, wto)
      | (Some wto, None) -> (update, wto)
    in
    let marked = ref vs in
    let is_marked v = VSet.mem v (!marked) in
    let mark v = marked := VSet.add v (!marked) in
    let unmark v = marked := VSet.remove v (!marked) in
    let update v =
      let changed = is_marked v && (incr evaluations; update v) in
      unmark v;
      if changed then G.iter_succ mark graph v;
      changed
    in
    let rec fix = function
      | WSimple x -> update x
      | WLoop xs ->
	let f changed x = fix x || changed in
	let rec loop changed =
	  if List.fold_left f false xs
	  then loop true
	  else changed
	in
	loop false
    in
    List.iter (fun elt -> ignore (fix elt)) wto;
    Log.logf ~level:Log.fix "Evaluations: %d" (!evaluations)
end

type 'a worklist =
  { pick : unit -> ('a * 'a worklist) option;
    add_succs : 'a -> 'a worklist }

(** Compute a fixpoint using a worklist *)
let fix_worklist worklist update =
  let rec fix worklist =
    match worklist.pick () with
    | Some (elt, worklist) ->
      if update elt then fix (worklist.add_succs elt)
      else fix worklist
    | None -> ()
  in
  fix worklist

(** Default instantiation of the worklist algorithm, where worklist items are
    vertices of a graph, and the successors of an item are its succesors in
    the graph. *)
module GraphWorklist
  (G : Graph.Sig.G)
  (C : sig val compare : G.V.t -> G.V.t -> int end) =
struct
  module VSet = Set.Make(struct
			   type t = G.V.t
			   let compare = C.compare
			 end)
  let rec create_worklist graph set =
    let pick () =
      if VSet.is_empty set then None
      else begin
	let x = VSet.min_elt set in
	Some (x, create_worklist graph (VSet.remove x set))
      end
    in
    let add_succs v =
      create_worklist graph (G.fold_succ VSet.add graph v set)
    in
    { pick = pick;
      add_succs = add_succs }
  let fix graph ?init:(vs = G.fold_vertex VSet.add graph VSet.empty) update =
    fix_worklist (create_worklist graph vs) update
end

module MakeAnalysis (G : G) (D : Sig.AbstractDomain.S) : sig
  type result
  val analyze :
    (G.V.t -> D.t -> D.t) ->
    ?edge_transfer:(G.E.t -> D.t -> D.t) ->
    G.t ->
    result
  val input : result -> G.V.t -> D.t
  val output : result -> G.V.t -> D.t
  val enum_input : result -> (G.V.t * D.t) BatEnum.t
  val enum_output : result -> (G.V.t * D.t) BatEnum.t
end = struct
  module HT = BatHashtbl.Make(G.V)
  module Fix = Wto(G)
  type result =
    { map : D.t HT.t;
      pred : G.E.t list HT.t;
      edge_transfer :  G.E.t -> D.t -> D.t }

  let populate_pred graph =
    let pred = HT.create 991 in
    let add_edge e =
      let dst = G.E.dst e in
      HT.add pred dst (e::(HT.find pred dst))
    in
    G.iter_vertex (fun v -> HT.add pred v []) graph;
    G.iter_edges_e add_edge graph;
    pred

  let prop result vertex =
    try HT.find result.map vertex
    with Not_found -> D.bottom

  let input result vertex =
    let predecessors =
      try HT.find result.pred vertex with Not_found -> assert false
    in
    match predecessors with
    | [] -> D.bottom
    | _ ->
      BatList.reduce D.join (List.map (fun e ->
	result.edge_transfer e (prop result (G.E.src e))
      ) predecessors)

  let analyze transfer ?(edge_transfer=fun _ v -> v)  graph =
    let result =
      { map = HT.create 991;
	pred = populate_pred graph;
	edge_transfer = edge_transfer }
    in
    let update join vertex =
      let flow_out = transfer vertex (input result vertex) in
      if HT.mem result.map vertex then begin
	let old_prop = prop result vertex in
	let new_prop = join old_prop flow_out in
	let changed = not (D.equal old_prop new_prop) in
	if changed then HT.replace result.map vertex new_prop;
	changed
      end else begin
	Log.errorf "FRESH (%d)" (HT.length result.map);
	HT.add result.map vertex flow_out;
	true
      end
    in
    Fix.fix graph (update D.join) (Some (update D.widen));
    result

  let output result vertex = HT.find result.map vertex

  let enum_input result =
    BatEnum.map (fun v -> (v, input result v)) (HT.keys result.pred)

  let enum_output result = HT.enum result.map
end

