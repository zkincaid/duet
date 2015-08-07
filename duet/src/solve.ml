(** Solve an abstract interpretation problem.  This module contains
    two analyses ({!IntervalAnalysis} and {!OctagonAnalysis}) that
    check that array accesses are within bounds using two different
    numerical domains. *)
module S = Set
open Core
open Apak
open Ai
open CfgIr

module Pack = Afg.Pack

include Log.Make(struct let name = "solve" end)

(** Number of times a widening vertex can be evaluated before widening is
    applied *)
let widening_limit = ref 1

(** Graph signature for the solve functors *)
module type G = sig
  type t
  module V : Graph.Sig.VERTEX
  module E : Graph.Sig.EDGE with type vertex = V.t
  val iter_vertex : (V.t -> unit) -> t -> unit
  val iter_succ : (V.t -> unit) -> t -> V.t -> unit
  val fold_vertex : (V.t -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_edges : (V.t -> V.t -> 'a -> 'a) -> t -> 'a -> 'a
  val iter_edges_e : (E.t -> unit) -> t -> unit
  val nb_vertex : t -> int
  val nb_edges : t -> int
  val mem_vertex : t -> V.t -> bool
  val fold_succ : (V.t -> 'a -> 'a) -> t -> V.t -> 'a -> 'a
end

module type MinAnalysis = sig
  type absval
  type st (** Some arbitrary state used by the analysis.  If no state is
              required, st should just be unit *)
  module G : G
  val eval : st -> G.t -> (G.V.t -> absval) -> G.V.t -> absval
  val join : st -> G.V.t -> absval -> absval -> absval option
  val widen : (st -> G.V.t -> absval -> absval -> absval option) option
  val name : string
  val pp_vertex : Format.formatter -> G.V.t -> unit
  val pp_absval : Format.formatter -> absval -> unit
end

module MkMin (A : MinAnalysis) : sig
  type result
  val get_state : result -> A.st
  val get_graph : result -> A.G.t
  val do_analysis : A.st -> A.G.t -> (A.G.V.t -> A.absval) -> result
  val solve : result -> A.G.V.t list -> unit
  val lookup : result -> A.G.V.t -> A.absval
  val display : ?widening : (A.G.V.t -> bool) -> result -> unit
  val enum_result : result -> (A.G.V.t * A.absval) BatEnum.t
  val empty_result : A.st -> A.G.t -> result
  val init_result : result -> A.G.t -> (A.G.V.t -> A.absval) -> unit
end = struct
  module G = A.G
  module HT = BatHashtbl.Make(G.V)
  type result = { map : A.absval HT.t;
                  graph : A.G.t;
                  state : A.st }

  let get_state r = r.state
  let get_graph r = r.graph
  let lookup result def =
    try HT.find result.map def
    with Not_found -> begin
        Log.errorf "No property associated with vertex %a"
          A.pp_vertex def;
        assert false
      end

  let empty_result state graph =
    { map = HT.create 991;
      graph = graph;
      state = state }

  let init_result result graph f =
    G.iter_vertex (fun v -> HT.add result.map v (f v)) graph

  module Fix = Fixpoint.Wto(G)

  (* solve implementation *)
  let solve_impl result worklist =
    let graph = result.graph in
    let update join vertex =
      let value = A.eval result.state result.graph (lookup result) vertex in
      if HT.mem result.map vertex then begin
        let old_value = lookup result vertex in
        match join result.state vertex old_value value with
        | Some new_value -> (HT.replace result.map vertex new_value; true)
        | None -> false
      end else (HT.add result.map vertex value; true)
    in
    let wide_update = match A.widen with
      | Some widen -> Some (update widen)
      | None       -> None
    in
    let worklist = List.fold_right Fix.VSet.add worklist Fix.VSet.empty in
    logf "Vertices: %d" (G.nb_vertex graph);
    logf "Edges: %d" (G.nb_edges graph);
    Fix.fix result.graph ~init:worklist (update A.join) wide_update

  let solve result =
    Log.phase ("Fixpoint computation: " ^ A.name) (solve_impl result)

  let do_analysis state graph initial_value =
    let result = empty_result state graph in
    let worklist = G.fold_vertex (fun x xs -> x::xs) graph [] in
    G.iter_vertex (fun v -> HT.add result.map v (initial_value v)) graph;
    solve result worklist;
    result

  (** Display an AFG with vertices annotated with the abstract values
      from map to the screen *)
  let display ?(widening = (fun _ -> false)) result = 
    let module Show_v = struct
      type t = G.V.t
      let pp formatter v =
        Format.fprintf formatter "%a@\n%a"
          A.pp_vertex v
          A.pp_absval (lookup result v)
    end in
    let module D = ExtGraph.Display.MakeSimple(G)(Show_v) in
    D.display result.graph

  let enum_result result = HT.enum result.map
end

module type Analysis = sig
  type absval
  type st (** Some arbitrary state used by the analysis.  If no state is
              required, st should just be unit *)
  module G : G
  val transfer : st -> absval -> G.V.t -> absval
  val flow_in : st -> G.t -> (G.V.t -> absval) -> G.V.t -> absval
  val join : st -> G.V.t -> absval -> absval -> absval option
  val widen : (st -> G.V.t -> absval -> absval -> absval option) option
  val name : string
  val pp_vertex : Format.formatter -> G.V.t -> unit
  val pp_absval : Format.formatter -> absval -> unit
end

module Mk (A : Analysis) : sig
  type result
  val do_analysis : A.st -> A.G.t -> (A.G.V.t -> A.absval) -> result
  val solve : result -> A.G.V.t list -> unit
  val input : result -> A.G.V.t -> A.absval
  val output : result -> A.G.V.t -> A.absval
  val display : ?widening : (A.G.V.t -> bool) -> result -> unit
  val enum_input : result -> (A.G.V.t * A.absval) BatEnum.t
  val enum_output : result -> (A.G.V.t * A.absval) BatEnum.t
  val empty_result : A.st -> A.G.t -> result
  val init_result : result -> A.G.t -> (A.G.V.t -> A.absval) -> unit
end = struct
  module G = A.G
  module HT = Hashtbl.Make(G.V)

  let eval st graph lookup vertex =
    logf "Transfer %a@\n" A.pp_vertex vertex;

    let input = A.flow_in st graph lookup vertex in
    logf "Input:@\n%a@\n" A.pp_absval input;

    (* Don't compute output until input is printed - it gives us better
       traces. *)
    let output = A.transfer st input vertex in
    logf "Output:@\n%a@\n" A.pp_absval output;

    output

  module MinSolver = MkMin(struct
      include A
      let eval = eval
    end)

  type result = MinSolver.result

  let input result vertex =
    A.flow_in
      (MinSolver.get_state result)
      (MinSolver.get_graph result)
      (MinSolver.lookup result)
      vertex
  let output result vertex =
    eval
      (MinSolver.get_state result)
      (MinSolver.get_graph result)
      (MinSolver.lookup result)
      vertex

  let empty_result = MinSolver.empty_result
  let init_result = MinSolver.init_result
  let solve = MinSolver.solve
  let do_analysis = MinSolver.do_analysis
  let display = MinSolver.display

  let enum_output = MinSolver.enum_result
  let enum_input result =
    (* todo: build vertex enum more efficiently *)
    let vertices =
      G.fold_vertex (fun v vs -> v::vs) (MinSolver.get_graph result) []
    in
    BatEnum.map (fun v -> (v, input result v)) (BatList.enum vertices)

end

module MakeAfgSolver (I : Interpretation) =
struct
  module G = Afg.G
  module A = struct
    module G = G
    type absval = I.t
    type st = { mutable widening : int Def.HT.t }

    let lookup_widening st def =
      try
        let limit = Def.HT.find st.widening def in
        Def.HT.replace st.widening def (limit - 1);
        limit
      with Not_found -> begin
          Def.HT.add st.widening def (!widening_limit);
          (!widening_limit)
        end

    let transfer _ flow_in def = I.transfer def flow_in

    let flow_in _ graph val_map def =
      let add_pred e map =
        let label = G.E.label e in
        let pre_state = Pack.project_fst label in
        let absval = I.inject (val_map (G.E.src e)) pre_state in
        let state = Pack.project_snd label in
        let old = (try Pack.SetMap.find state map
                   with Not_found -> I.bottom state)
        in
        let rename_map =
          let f a xs = (Pack.fst a, Pack.snd a)::xs in
          Pack.PairSet.fold f label []
        in
        let new_val =
          (* This injection is required by coarsen, since it adds a fake
             REACHABLE variable *)
          I.inject (I.rename (I.project absval pre_state) rename_map) state
        in
        Pack.SetMap.add state (I.join old new_val) map
      in
      let map = G.fold_pred_e add_pred graph def Pack.SetMap.empty in
      let domain = G.domain graph def in
      let combine _ v rest = I.meet (I.inject v domain) rest in
      match def.dkind with
      | Initial -> I.top (G.codomain graph def)
      | _ -> Pack.SetMap.fold combine map (I.top domain)

    let join st def old_val new_val =
      let new_val = I.join old_val new_val in
      if I.equal old_val new_val then None else Some new_val

    let widen_impl st def old_val new_val =
      let new_val = I.join old_val new_val in
      if I.equal old_val new_val then None else begin
        let limit = lookup_widening st def in
        if limit >= 0 then Some new_val
        else match def.dkind with
          | Assume c | Assert (c, _) ->
            Some (I.transfer def (I.widen old_val new_val))
          | _ -> Some (I.widen old_val new_val)
      end
    let widen = Some widen_impl

    let name = I.name
    let pp_vertex = Def.pp
    let pp_absval = I.pp
  end
  module S = Mk(A)
  include S

  let mk_state _ = { A.widening = Def.HT.create 64 }

  let reset_state st _ = Def.HT.clear st.A.widening

  (* override default do_analysis *)
  let do_analysis st graph =
    do_analysis st graph (fun _ -> I.bottom (AP.Set.empty))

  (** Full error report *)
  let error_report graph map =
    let check_assertion v =
      match v.dkind with
      | Assert (expr, _) ->
        let env = S.input map v in
        if I.assert_true expr env
        then Log.log ~level:`always (string_of_int v.did ^ " PASS")
        else Log.log ~level:`always (string_of_int v.did ^ " FAIL")
      | AssertMemSafe (expr, _) ->
        let env = S.input map v in
        if I.assert_memsafe expr env
        then Log.log ~level:`always (string_of_int v.did ^ " PASS")
        else Log.log ~level:`always (string_of_int v.did ^ " FAIL")
      | _ -> ()
    in
    G.iter_vertex check_assertion graph

  (** Find and report assertion violations *)
  let check_assertions graph map =
    let log_failure def msg value =
      Report.log_errorf
        (Def.get_location def)
        "Assertion failed: %s@\n%a" msg I.pp value
    in
    let log_memsafe_failure def msg value =
      Report.log_errorf
        (Def.get_location def)
        "Cannot prove safe: %s@\n%a" msg I.pp value
    in
    let check_assertion v =
      match v.dkind with
      | Assert (expr, msg) ->
        let env = S.input map v in
        if not (I.assert_true expr env)
        then log_failure v msg env
        else Report.log_safe ()
      | AssertMemSafe (expr, msg) ->
        let env = S.input map v in
        if not (I.assert_memsafe expr env)
        then log_memsafe_failure v msg env
        else Report.log_safe ()
      | _ -> ()
    in
    G.iter_vertex check_assertion graph;
    Report.print_errors ();
    Report.print_safe ()
end

module MakeForwardCfgSolver (I : MinInterpretation) = struct
  module A = struct
    module G = Cfg
    type absval = I.t
    type st = def -> def -> int (* reverse postorder *)

    let transfer _ input def = I.transfer def input

    let flow_in _ graph val_map v =
      G.fold_pred (fun v value -> I.join (val_map v) value) graph v I.bottom

    let join _ _ x y =
      let newv = I.join x y in
      if I.equal x newv then None else Some newv
    let widen = None
    let name = I.name
    let pp_vertex = Def.pp
    let pp_absval = I.pp
  end
  module S = Mk(A)
  include S

  (* override default do_analysis *)
  let do_analysis graph =
    do_analysis (Cfg.reverse_postorder graph) graph

  let file_analysis file f initial mk_init =
    (* save the output abstract value of each fork, so that it may be used as
       the input of the initial vertex of the created thread *)
    let fork_map = Def.HT.create 32 in

    let mk_initial_fun cfg init =
      let iv = Cfg.initial_vertex cfg in
      fun v -> if Def.equal v iv then init else I.bottom
    in
    let process_cfg cfg init =
      let result = do_analysis cfg (mk_initial_fun cfg init) in
      let add_fork (def, value) = match def.dkind with
        | Builtin (Fork _) -> Def.HT.add fork_map def value
        | _ -> ()
      in
      BatEnum.iter add_fork (enum_output result);
      f result;
      result
    in
    let initial =
      match file.globinit with
      | None -> initial
      | Some func ->
        let f init (v, v_value) = match v.dkind with
          | Return _ -> I.join v_value init
          | _ -> init
        in
        let result = process_cfg func.cfg initial in
        BatEnum.fold f I.bottom (S.enum_output result)
    in
    let process_thread def thread =
      let initial = match def with
        | Some fork ->
          (try Def.HT.find fork_map fork
           with Not_found ->
             failwith "solve/forwardCfgSover: No entry for fork")
        | None -> initial
      in
      let func = lookup_function thread file in
      ignore (process_cfg func.cfg (mk_init func initial))
    in
    Call.iter_tcg_order process_thread file
end

module MakeBackwardCfgSolver (I : MinInterpretation) = struct
  module A = struct
    module G = ExtGraph.Reverse(Cfg)
    type absval = I.t
    type st = { thread_map : varinfo -> I.t }

    let transfer st input def =
      I.transfer def input

    let flow_in st graph val_map v =
      let input =
        Cfg.fold_succ (fun v value -> I.join (val_map v) value) graph v I.bottom
      in
      match v.dkind with
      | Builtin (Fork (_, tgt, _)) ->
        let join func acc = I.join (st.thread_map func) acc in
        Varinfo.Set.fold join (PointerAnalysis.resolve_call tgt) input
      | _ -> input

    let join st def x y =
      if I.equal x y then None else Some (I.join x y)
    let widen = None

    let name = I.name
    let pp_vertex = Def.pp
    let pp_absval = I.pp
  end
  module S = Mk(A)
  include S

  (* override default do_analysis *)
  let do_analysis graph =
    let state =
      { A.thread_map = (fun _ -> failwith "No interpretation for fork") }
    in
    do_analysis state graph

  module W = ExtGraph.Subgraph(Cfg)

  let backwards_file_analysis file f initial mk_init =
    let mk_initial_fun cfg init v =
      if Cfg.is_terminal v cfg then init else I.bottom
    in
    let thread_map = Hashtbl.create 16 in
    let lookup_thread x =
      try Hashtbl.find thread_map x
      with Not_found -> assert false
    in
    let do_analysis graph =
      let st = { A.thread_map = lookup_thread }
      in
      S.do_analysis st graph
    in
    let process_cfg cfg init =
      let result = do_analysis cfg (mk_initial_fun cfg init) in
      f result;
      result
    in
    let initial_value = ref I.bottom in
    let process_thread _ thread =
      let func = lookup_function thread file in
      let result = process_cfg func.cfg (mk_init func initial) in
      let thread_value = S.output result (Cfg.initial_vertex func.cfg) in
      Hashtbl.add thread_map thread thread_value;
      Cfg.sanity_check func.cfg;
      if List.exists (Varinfo.equal thread) file.entry_points
      then initial_value := I.join (!initial_value) thread_value
    in
    Call.iter_reverse_tcg_order process_thread file;
    (match file.globinit with
     | None -> !initial_value
     | Some func ->
       let result = process_cfg func.cfg (!initial_value) in
       S.output result (Cfg.initial_vertex func.cfg))
end
