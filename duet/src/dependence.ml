(** Dependence analysis *)
open Core
open CfgIr
open Solve
open Ai
open Apak

module Pack = Var.Set
module DefEnum = Enumeration.Make(Def)
module PackEnum = Enumeration.Make(Pack)

let lower_opt = function
  | Some x -> x
  | None -> 0

let may_assign_vars def =
  match Def.assigned_var def with
  | Some v -> Var.Set.singleton v
  | None -> begin match def.dkind with
      | Store (lhs, _) ->
        let f memloc set =
          match memloc with
          | (Pa.MAddr vi, offset) -> Var.Set.add (vi, offset) set
          | _ -> set
        in
        Pa.MemLoc.Set.fold f (Pa.resolve_ap lhs) Var.Set.empty
      | _ -> Var.Set.empty
    end

(* Does a given location define a condition (i.e., does it define a
   variable that occurs in a condition)? *)
let defines_cond def pred =
  let pred_vars = Bexpr.free_vars pred in
  let assigned_vars = may_assign_vars def in
  not (Var.Set.is_empty (Var.Set.inter pred_vars assigned_vars))

module AtomicityAnalysis = Solve.MakeForwardCfgSolver(
  struct

    (* We should only encounter access paths *)
    type t = int option deriving (Show)
    let format = Show_t.format
    let show = Show_t.show
    let join x y = match x,y with
      | (None, x) | (x, None) -> x
      | (Some x, Some y) -> Some (min x y)
    let widen = join
    let equal = (=)

    let transfer def flow_in =
      let flow_in = lower_opt flow_in in
      match def.dkind with
      | Builtin AtomicBegin -> Some (flow_in + 1)
      | Builtin AtomicEnd -> Some (flow_in - 1)
      | _ -> Some flow_in

    let name = "Atomicity analysis"
    let bottom = None
  end)

(* Retrieve a list of lock-typed global variables from a program *)
let extract_locks file =
  let f rest var =
    let is_lock var = resolve_type (AP.get_type (Variable var)) = Lock in
    let add x rest = (Variable x)::rest in
    Var.Set.fold add (Var.Set.filter is_lock (get_offsets var)) rest
  in
  List.fold_left f [] file.vars

(* map from abstract booleans to an integer representation *)
let int_of_ab = function
  | Top    -> 0
  | Yes    -> 1
  | No     -> 2
  | Bottom -> 3

(* datalog conjunction *)
let (&&&) x y = x ^ "," ^ y
(* datalog logical negation *)
let neg x = "!" ^ x

(* The core of the dependence analysis.  Should not be exported.
   Called via run. *)
module Dependence (M : sig
    type t (** APRON type *)
    val man : t Apron.Manager.t (** APRON manager *)
    val file : file
    val dir : string (** temp directory for dep analysis *)
    val pack : var -> Pack.t
  end) = struct
  module State = Afg.Pack

  (* Retrieve a list of predicates from a program that will be used as
     control conditions.  Each of these predicates must be defined only
     over global access paths.  Currently, predicates are extracted only
     from thread bodies. *)
  let extract_predicates file =
    let is_constant p =
      (* don't bother keeping trivial predicates *)
      match Bexpr.eval p with
      | Some _ -> true
      | None -> false
    in
    let is_shared_var ap =
      match ap with
      | Deref _ -> false
      | Variable v ->
        (Varinfo.is_shared (fst v)) && (is_numeric_type (Var.get_type v))
    in
    let f vertex preds = match vertex.dkind with
      | Assert (p, _) | Assume p ->
        if (not (is_constant p)
            && AP.Set.for_all is_shared_var (Bexpr.get_uses p))
        then begin
          (* don't add p if it is logically equivalent to some other extracted
             predicate or its negation *)
          let p = Bexpr.simplify p in
          let not_p = Bexpr.negate p in
          let equiv_p q = Bexpr.equal q p || Bexpr.equal q not_p in
          if not (List.exists equiv_p preds) then p::preds
          else preds
        end else preds
      | _ -> preds
    in
    let preds =
      let process_thread p t =
        let func = lookup_function t file in
        Cfg.fold_vertex f func.cfg p
      in
      List.fold_left process_thread [] file.threads
    in
    Log.log "Extracted predicates:";
    List.iter
      (fun p -> Log.log_pp Bexpr.format p)
      preds;
    preds

  (* The datalog solver only knows about integers, so we need def/ap
     enumerations to map back and forth between defs/aps and the
     integer representations. *)
  let def_enum = DefEnum.empty ()
  let id_of_def = DefEnum.to_int def_enum
  let def_of_id = DefEnum.from_int def_enum

  let pack_enum = PackEnum.empty ()
  let id_of_pack = PackEnum.to_int pack_enum
  let pack_of_id = PackEnum.from_int pack_enum

  let file = M.file
  let predicates = extract_predicates file
  let locks = extract_locks file

  let is_shared_pack pack = Pack.for_all Var.is_shared pack

  (* Datalog solver object *)
  let d =
    let solver = new Datalog.monolithicSolver M.dir "dependence" in
    solver#new_domain "ABSBOOL";
    solver#new_domain "LOC";
    solver#new_domain "AP";
    solver#new_domain "COND";
    solver#ensure_domain_capacity "ABSBOOL" 4;
    solver

  (* Dummy vertex that is added as a control flow predecessor of every
     initial vertex.  If file.globinit is defined, initial_vertex is
     just added as a predecessor of file.globinit's initial vertex.
     Otherwise, initial_vertex is addes as a predecessor of every
     thread's initial vertex.  *)
  let initial_def = Def.mk (Assume Bexpr.ktrue)

  module I = IExtra(ApronInterpretation)
  module DG = Afg.G
  module NumAnalysis = Solve.MakeAfgSolver(I)

  let may_use def =
    let f uses p =
      if defines_cond def p then Var.Set.union (Bexpr.free_vars p) uses
      else uses
    in
    List.fold_left f (Live.may_use def) predicates

  (***************************************************************************)
  (* begin datalog stuff *****************************************************)
  (* channels *)
  let e_def = d#input_tuples "defines" [("LOC",0);("AP",0)]
  let e_kill = d#input_tuples "kill" [("LOC",0);("AP",0)]
  let e_use = d#input_tuples "uses" [("LOC",0);("AP",0)]
  let e_succ = d#input_tuples "succ" [("LOC",0);("LOC",1)]
  let e_definesCond =
    d#input_tuples "definesCond" [("COND", 0);("LOC",0);("ABSBOOL",0)]
  let e_blockCond =
    d#input_tuples "blockCond" [("COND", 0);("LOC",0);("ABSBOOL",0)]
  let e_spawn = d#input_tuples "spawn" [("LOC",0);("LOC",1)]
  let e_atomic = d#input_tuples "atomic" [("LOC",0)]
  let holding_chans =
    let holding_chan n _ =
      d#input_tuples ("holding" ^ (string_of_int n)) [("LOC",0)]
    in
    BatList.mapi holding_chan locks
  let acquire_chans =
    let acquire_chan n _ =
      d#input_tuples ("acquire" ^ (string_of_int n)) [("LOC",0)]
    in
    BatList.mapi acquire_chan locks

  (* Emits static structure: CFG successor relation, lockset
     information, and thread creation information.  This is the
     information that doesn't need to be updated at every round of the
     coarsening loop. *)
  let emit_static_structure () =
    let add_succ u v = e_succ [id_of_def u; id_of_def v] in
    let emit_locks (vertex, ls) =
      (match vertex.dkind with
       | Builtin (Acquire (AddrOf lock)) ->
         List.iter2
           (fun l emit -> if AP.equal l lock then emit [id_of_def vertex])
           locks
           acquire_chans
       | _ -> ());
      (List.iter2
         (fun lock emit -> if AP.Set.mem lock ls then emit [id_of_def vertex])
         locks
         holding_chans)
    in
    let emit_atomic (vertex, atomicity_level) =
      if (lower_opt atomicity_level) > 0 then e_atomic [id_of_def vertex]
    in
    let emit_def_use def =
      begin match Def.assigned_var def with
        | Some v -> begin
            let p = M.pack v in
            if is_shared_pack p then begin
              e_def [id_of_def def; id_of_pack p];
              e_kill [id_of_def def; id_of_pack p]
            end
          end
        | None -> match def.dkind with
          | Store (lhs, rhs) ->
            let f memloc =
              match memloc with
              | (Pa.MAddr vi, offset) ->
                let p = M.pack (vi, offset) in
                if is_shared_pack p then
                  e_def [id_of_def def; id_of_pack p]
              | (_, _) -> ()
            in
            Pa.MemLoc.Set.iter f (Pa.resolve_ap lhs)
          | Assume phi | Assert (phi, _) ->
            let set_rd v =
              let p = M.pack v in
              if is_shared_pack p then e_kill [id_of_def def; id_of_pack p]
            in
            Var.Set.iter set_rd (Bexpr.free_vars phi)
          | _ -> ()
      end;

      (* emit uses *)
      Var.Set.iter
        (fun var ->
           let pack = M.pack var in
           if is_shared_pack pack then e_use [id_of_def def; id_of_pack pack])
        (may_use def)
    in

    (* emit static structure of a single cfg.  This includes the
       successor relation, defs/uses, and lock information. *)
    let emit_cfg cfg =
      let init_vertex = Cfg.initial_vertex cfg in
      let all_locks = List.fold_right AP.Set.add locks AP.Set.empty in

      (* Lockset analysis: what locks must be held at each point? *)
      let module LSAnalysis = Solve.MakeForwardCfgSolver(
        struct
          (* We should only encounter access paths *)
          include Lattice.Dual(Lattice.LiftSubset(AP.Set))

          let transfer def = match def.dkind with
            | Builtin (Acquire (AddrOf lock)) -> AP.Set.add lock
            | Builtin (Release (AddrOf lock)) -> AP.Set.remove lock
            | _ -> (fun ls -> ls)

          let widen = join
          let name = "Lockset analysis"
          let bottom = all_locks
        end)
      in
      let init_ls v =
        if v.did = init_vertex.did then AP.Set.empty else all_locks
      in
      Cfg.iter_edges add_succ cfg;
      Cfg.iter_vertex emit_def_use cfg;
      BatEnum.iter
        emit_locks
        (LSAnalysis.enum_input (LSAnalysis.do_analysis cfg init_ls));
      BatEnum.iter
        emit_atomic
        (AtomicityAnalysis.enum_input
           (AtomicityAnalysis.do_analysis cfg (fun _ -> None)))
    in

    (* Emit initial coreachable pairs.  If the program is
       parameterized, all pairs of initial statements are coreachable.
       If not, then only initial statements of distinct threads are
       coreachable. *)
    let thread_cfg thread =
      let func = lookup_function thread file in
      func.cfg
    in
    let thread_init_vertex thread = Cfg.initial_vertex (thread_cfg thread) in
    let init_vertex_str thread =
      string_of_int (id_of_def (thread_init_vertex thread))
    in
    let emit_coreachable x y =
      d#emit ("coreachable(" ^ (init_vertex_str x) ^ ","
              ^ (init_vertex_str y) ^").")
    in
    let coreach =
      if !CmdLine.parameterized && not (!CfgIr.whole_program)
      then (fun (x, y) -> emit_coreachable x y)
      else (fun (x, y) ->
          if not (Varinfo.equal x y)
          then emit_coreachable x y)
    in

    (* iterate f over the initial vertices of each thread *)
    let iter_thread_init f =
      List.iter (fun t -> f (thread_init_vertex t)) file.threads
    in
    List.iter (fun thread -> emit_cfg thread.cfg) file.funcs;

    (* emit spawn relation *)
    Call.iter_tcg_order
      (fun def thread ->
         let init_vertex = thread_init_vertex thread in
         match def with
         | Some def ->
           e_spawn [id_of_def def; id_of_def init_vertex]
         | None -> ())
      file;

    let entries = file.entry_points in
    let enum =
      Putil.cartesian_product (BatList.enum entries) (BatList.enum entries)
    in
    BatEnum.iter coreach enum;

    (* Add in dummy CFG successor edges.  This is necessary for *)
    match file.globinit with
    | Some init ->
      emit_cfg init.cfg;
      add_succ initial_def (Cfg.initial_vertex init.cfg);
      BatEnum.iter
        (fun d -> iter_thread_init (add_succ d))
        (Cfg.enum_terminal init.cfg)
    | None -> iter_thread_init (add_succ initial_def)

  (* end emit_static_structure ***********************************************)

  (****************************************************************************
   ** Generate the datalog program for the interference analysis
   ***************************************************************************)
  let emit_datalog () =
    let emit = d#emit in
    let tuple x = "(" ^ (String.concat "," x) ^ ")" in
    let binary_relation name (x,y) = name ^ (tuple [x;y]) in
    let ternary_relation name (x,y,z) = name ^ (tuple [x;y;z]) in
    let indexed_binrel name i = binary_relation (name ^ (string_of_int i)) in
    let indexed_unrel name i x = name ^ (string_of_int i) ^ (tuple [x]) in

    (* input relations *******************************************************)
    let succ = binary_relation "succ" in
    let defines = binary_relation "defines" in
    let uses = binary_relation "uses" in
    let definesCond = ternary_relation "definesCond" in
    let blockCond = ternary_relation "blockCond" in
    let holding = indexed_unrel "holding" in
    let acquire = indexed_unrel "acquire" in
    let spawn = binary_relation "spawn" in

    (* kill(a,ap) holds if a is a location that defines ap, but the
       definition of ap is not globally visible *)
    let kill = binary_relation "kill" in
    let atomic x = "atomic" ^ (tuple [x]) in

    (* computed relations ****************************************************)
    let consistent = binary_relation "consistent" in
    let enabledCond = ternary_relation "enabledCond" in
    let enabledLock = indexed_binrel "enabledLock" in
    let enabled = binary_relation "enabled" in
    let coreachable = binary_relation "coreachable" in
    let inv = ternary_relation "inv" in (* invariant map *)
    let mayReach = ternary_relation "mayReach" in

    (* mayReach_impl(a,ap,b,c) holds if a defines ap, and there is a
       pseudotrace from (a,_) to (b,c) (where b is location in a's thread
       and c is a location in another thread) on which there is no
       definition to ap. *)
    let mayReach_impl (a,b,c,d) = "mayReach_impl" ^ (tuple [a;b;c;d]) in

    (* Similar to mayReach_impl: mayReachCond(c,x,y,z) holds if x
       defines the condition c, and there is a pseudotrace from (x,_)
       to (y,z) (where y is a location in x's thread and z is a
       location in another thread) on which there is no definition to
       c. *)
    let mayReachCond (a,b,c,d) = "mayReachCond" ^ (tuple [a;b;c;d]) in

    (* localMayReachCond(c,a,b) holds if a is a location that defines
       condition c, and there is a CFG path from a to b along which there
       is no other definition to c. *)
    let localMayReachCond = ternary_relation "localMayReachCond" in

    (* relevant(a,ap) holds if there is a CFG path from a to a use of
       ap along which there are no definitions to ap *)
    let relevant = binary_relation "relevant" in

    (* desc(a,b) holds (b is a /descendent/ of a) if there is a CFG
       path from a to b along which there are no blocking
       transitions.  *)
    let desc = binary_relation "desc" in

    (* descAP(a,b,ap) holds if there is a CFG path from a to b along
       which there are no blocking transitions or definitions to ap
       (internally on the path -- a or b may block or define ap) *)
    let descAP = ternary_relation "descAP" in

    let descCond = ternary_relation "descCond" in

    (* blocksOnCond(c,a) holds if a is a location that blocks on condition c *)
    let blocksOnCond = binary_relation "blocksOnCond" in

    (* killCond(c,a) holds if a is a location that defines the condition c *)
    let killCond = binary_relation "killCond" in

    let nonblocking x = "nonblocking" ^ (tuple [x]) in

    (*************************************************************************)
    (* conjunction of every element in a list *)
    let list_and = String.concat "," in

    (* true iff location x is nonblocking (derived relation) *)
    let conj_nonblocking x rest =
      let cond_block =
        BatList.mapi
          (fun n _ -> neg (blocksOnCond ((string_of_int n), x)))
          predicates
      in
      let lock_block =
        BatList.mapi (fun n _ -> neg (acquire n x)) locks
      in
      let conditions = cond_block@lock_block
      in
      if List.length conditions > 0 then (list_and conditions) &&& rest
      else rest
    in

    (* variables *)
    let a_pred = "aPred" in
    let b_pred = "bPred" in
    let c_pred = "cPred" in
    let i = "i" in
    let a = "a" in
    let b = "b" in
    let c = "c" in
    let def = "def" in
    let ap = "ap" in
    let use = "use" in
    let v = "v" in

    let (<--) x y = emit (x ^ " :- " ^ y ^ ".") in
    emit ".bddvarorder AP0_COND0_COND1_COND2_COND3_COND4_ABSBOOL0_ABSBOOL1_LOC0_LOC1_LOC2_LOC3";

    BatList.iteri
      (fun n _ -> emit (enabledLock n ("a:LOC", "b:LOC")))
      locks;

    emit (enabledCond ("c:COND", "a:LOC", "b:LOC"));
    emit (mayReachCond ("c:COND", "a:LOC", "b:LOC", "c:LOC"));
    emit (localMayReachCond ("c:COND", "a:LOC", "b:LOC"));
    emit (blocksOnCond ("c:COND", "a:LOC"));
    emit (desc ("a:LOC", "b:LOC"));
    emit (descAP ("a:LOC", "b:LOC", "ap:AP"));
    emit (descCond ("a:LOC", "b:LOC", "c:COND"));
    emit (killCond ("c:COND", "a:LOC"));
    emit (inv ("c:COND", "a:LOC", "v:ABSBOOL"));
    emit (mayReach ("def:LOC", "ap:AP", "use:LOC") ^ " outputtuples");
    emit (mayReach_impl ("a:LOC", "ap:AP", "b:LOC", "c:LOC"));
    emit (enabled ("a:LOC", "b:LOC"));
    emit (coreachable ("ls:LOC", "rs:LOC"));
    emit (consistent("v1:ABSBOOL", "v2:ABSBOOL"));
    emit (relevant ("a:LOC", "ap:AP"));
    emit (nonblocking ("a:LOC"));

    emit (consistent ("0", "0") ^ ".");
    emit (consistent ("0", "1") ^ ".");
    emit (consistent ("0", "2") ^ ".");
    emit (consistent ("1", "0") ^ ".");
    emit (consistent ("2", "0") ^ ".");
    emit (consistent ("1", "1") ^ ".");
    emit (consistent ("2", "2") ^ ".");


    nonblocking(a) <-- conj_nonblocking a (neg(atomic(a)));

    (* descendents *********************************************************)
    desc (a,b) <-- succ(a,b);
    desc (a,c) <-- (desc(a,b) &&& nonblocking(b) &&& desc(b,c));
    descAP (a,b,"_") <-- succ(a,b);
    descAP (a,c,ap) <-- (descAP(a,b,ap)
                         &&& nonblocking b
                         &&& neg (kill(b,ap))
                         &&& descAP(b,c,ap));
    descCond (a,b,"_") <-- succ(a,b);
    descCond (a,c,i) <-- (descCond(a,b,i)
                          &&& nonblocking b
                          &&& (neg (killCond(i,b)))
                          &&& descCond(b,c,i));

    (* enabled *************************************************************)
    blocksOnCond(i,a) <-- (blockCond (i, a,"_"));
    enabledCond (i,a,b) <-- (inv (i, b, "bv") &&& blockCond (i, a, "av")
                             &&& consistent("av","bv"));
    enabledCond (i, a, "_") <-- (neg(blocksOnCond(i,a)));
    begin
      let f i _ =
        enabledLock i ("_",b) <-- (neg(holding i b));
        enabledLock i (a,"_") <-- (neg(acquire i a));
      in
      BatList.iteri f locks
    end;
    begin
      match (predicates, locks) with
      | ([], []) ->
        (* no locks or control conditions, so enabled always holds *)
        enabled("_",b) <-- neg(atomic(b));
      | _ ->
        let forall f = BatList.mapi (fun n _ -> f n) in
        let enabled_cond =
          forall
            (fun i -> enabledCond (string_of_int i, a, b))
            predicates
        in
        let enabled_lock =
          forall (fun i -> enabledLock i (a,b)) locks
        in
        enabled(a,b) <-- (neg(atomic(b))
                          &&& list_and (enabled_lock@enabled_cond))
    end;

    (* invariant map *******************************************************)
    killCond(i,a) <-- definesCond (i, a, "_");
    killCond(i,a) <-- blockCond (i, a, "_");

    mayReachCond(i,a,b,c) <-- (definesCond (i, a, "_") &&& coreachable(a, c)
                               &&& enabled(a, c) &&& succ(a,b));
    mayReachCond(i,a,b,c) <-- (mayReachCond (i, a, b_pred, c)
                               &&& descCond(b_pred, b, i)
                               &&& neg (killCond (i, b_pred))
                               &&& enabled(b_pred, c));
    mayReachCond(i,a,b,c) <-- (mayReachCond (i, a, b, c_pred)
                               &&& descCond(c_pred, c, i)
                               &&& neg (killCond (i, c_pred))
                               &&& enabled(c_pred, b));

    localMayReachCond(i,a,b) <-- (killCond(i, a) &&& succ(a,b));
    localMayReachCond(i,a,b) <-- (localMayReachCond(i, a, b_pred)
                                  &&& neg (killCond (i, b_pred))
                                  &&& descCond(b_pred, b, i));

    inv (i,b,v) <-- (localMayReachCond(i, a, b) &&& definesCond(i, a, v));
    inv (i,b,v) <-- (localMayReachCond(i, a, b) &&& blockCond(i, a, v));
    inv (i,b,v) <-- (mayReachCond (i, a, "_", b) &&& definesCond (i, a, v));

    (* coreachable *********************************************************)
    coreachable(a,b) <-- (coreachable(a_pred,b) &&& enabled(a_pred,b)
                          &&& desc(a_pred,a));
    coreachable(b,a) <-- (coreachable(b,a_pred) &&& enabled(a_pred,b)
                          &&& desc(a_pred,a));
    coreachable(b,c) <-- (spawn(a,b) &&& succ(a,c));
    coreachable(c,b) <-- (spawn(a,b) &&& succ(a,c));
    coreachable(a,c) <-- (coreachable(a,b) &&& spawn(b,c));
    coreachable(c,a) <-- (coreachable(a,b) &&& spawn(b,c));

    (* mayReach ************************************************************)
    mayReach(def,ap,use) <-- (defines(def,ap) &&& uses(use,ap)
                              &&& mayReach_impl(def,ap,"_",use));

    mayReach_impl (a,ap,b,c) <-- (defines(a,ap)
                                  &&& relevant(c,ap)
                                  &&& coreachable(a,c)
                                  &&& enabled(a,c)
                                  &&& descAP(a,b,ap));
    mayReach_impl (a,ap,b,c) <-- (mayReach_impl (a,ap,b_pred,c)
                                  &&& relevant(c,ap)
                                  &&& descAP(b_pred,b,ap)
                                  &&& neg (kill (b_pred, ap))
                                  &&& enabled(b_pred,c));
    mayReach_impl (a,ap,b,c) <-- (mayReach_impl (a,ap,b,c_pred)
                                  &&& relevant(c,ap)
                                  &&& descAP(c_pred,c,ap)
                                  &&& neg (kill (c_pred, ap))
                                  &&& enabled(c_pred,b));

    relevant(a,ap) <-- uses(a,ap);
    relevant(b,ap) <-- (neg(kill(b,ap))
                        &&& descAP(b,a,ap)
                        &&& relevant(a,ap))

  (* end emit_datalog ********************************************************)

  (* Does a given location block on a condition? *)
  let block_cond def pred = match def.dkind with
    | Assume p ->
      let np = Bexpr.simplify p in
      let neg_np = Bexpr.negate p in
      (Bexpr.equal np pred) || (Bexpr.equal neg_np pred)
    | _          -> false

  (* Emit invariant map (blockCond and definesCond).  This needs to be
     called at every round of the feedback loop. *)
  let emit_inv dg map =

    (* emit block/defines for a particular location and condition *)
    let go vertex post c_num pred =
      Log.debugf " emit_inv / Predicate: %a" Bexpr.format pred;
      let def_id = id_of_def vertex in
      if block_cond vertex pred then begin
        let ab = I.eval_pred pred (Lazy.force post) in
        e_blockCond [c_num; def_id; int_of_ab ab]
      end;
      if defines_cond vertex pred then begin
        let ab = I.eval_pred pred (Lazy.force post) in
        e_definesCond [c_num; def_id; int_of_ab ab]
      end
    in

    (* emit block/defines for a particular location *)
    let emit_inv_loc vertex = match vertex.dkind with
      | Initial -> ()
      | _ ->
        let post = lazy (NumAnalysis.output map vertex) in
        Log.debug ("emit_inv: " ^ (Def.show vertex));
        BatList.iteri (go vertex post) predicates
    in

    (* Treat the dummy initial vertex as a definition of each
       condition that assigns it the value top.  localReachCond will
       propagate this as appropriate, so that the invariant map at
       each location is completely defined by the reaching definitions
       of each condition *)
    let add_initial_def p _ =
      e_definesCond [p; id_of_def initial_def; int_of_ab Top]
    in
    DG.iter_vertex emit_inv_loc dg;
    BatList.iteri add_initial_def predicates

  (* end datalog stuff *******************************************************)
  (***************************************************************************)

  (* Create an edge from src to tgt, labelled with the set of access
     paths in ap's equivalence class *)
  let mk_edge src pack tgt =
    let label =
      let f var pair_set =
        let var = Variable var in
        State.PairSet.add (State.mk_pair var var) pair_set
      in
      Pack.fold f pack State.PairSet.empty
    in
    let label =
      match src.dkind with
      | Store (ap, _) ->
        let vars = Var.Set.inter pack (may_assign_vars src) in
        assert (Var.Set.cardinal vars == 1); (* todo *)
        let var = Variable (Var.Set.choose vars) in
        let label = State.PairSet.remove (State.mk_pair var var) label in
        State.PairSet.add (State.mk_pair ap var) label
      | _ -> label
    in
    DG.E.create src label tgt

  (* Encode the structure of the CFG via dependencies on a special "REACHABLE"
     variable.  This improves precision when an assertion is guarded by an
     unsatisfiable condition on which the assertion has no natural data
     dependence. *)
  let add_cfg_edges file dg =
    let reachable =
      let v =
        Variable (Var.mk (Varinfo.mk_local
                            "REACHABLE"
                            (Concrete (Int bool_width))))
      in
      State.PairSet.singleton (State.mk_pair v v)
    in
    let add_cfg_edge u v =
      DG.add_edge_e dg (DG.E.create u reachable v)
    in
    let add_cfg_edges cfg = Cfg.iter_edges add_cfg_edge cfg in
    let add_thread_edges t = add_cfg_edges (lookup_function t file).cfg in
    List.iter add_thread_edges file.threads;
    (match file.globinit with
     | Some f -> add_cfg_edges f.cfg
     | None -> ());
    dg

  (* Run the coarsen algorithm *)
  let run () =
    (* Add initial definitions for super accesspaths of a list of
       variables to a set of reaching definitions *)
    let dg = add_cfg_edges file (Dg.construct file M.pack may_use) in
    let worklist = ref [] in
    let add_edge = function
      | [def; ap; use] ->
        let def = def_of_id def in
        let pack = pack_of_id ap in
        let use = def_of_id use in
        let edge = mk_edge def pack use in
        if not (DG.mem_edge_e dg edge) then begin
          worklist := use::(!worklist);
          DG.add_edge_e dg edge
        end
      | _ -> failwith "Wrong arity for mayReach relation!"
    in
    let st = NumAnalysis.mk_state dg in
    let map = NumAnalysis.do_analysis st dg in
    (* a new interval analysis is computed before calling fix *)
    let rec fix () =
      Log.time "emit_inv" (emit_inv dg) map;
      d#run ();
      worklist := [];
      d#iter_tuples add_edge "mayReach";
      if !worklist != [] then begin
        if !CmdLine.display_graphs then NumAnalysis.display map;
        NumAnalysis.reset_state st dg;
        NumAnalysis.solve map (!worklist);
        fix ()
      end
    in
    emit_datalog ();
    emit_static_structure ();
    Log.debug "ENUM";
    Log.debug_pp (DefEnum.format Def.format) def_enum;
    if !CmdLine.display_graphs then NumAnalysis.display map;
    fix ();
    d#kill ();
    (dg, map)
end

(** Run interval analysis *)
let run file =
  let pack =
    if Ai.is_relational_domain () then InferFrames.infer_var_partition file
    else Var.Set.singleton
  in
  let run dir =
    let module R =
      Dependence(struct
        type t = Box.t
        let man = Box.manager_alloc ()
        let file = file
        let dir = dir
        let pack = pack
      end)
    in
    let (afg, map) = R.run () in
    R.NumAnalysis.check_assertions afg map
  in
  Putil.with_temp_dir "dep" run

let _ = CmdLine.register_pass ("-coarsen", run, " Coarsen algorithm (POPL'12)")
