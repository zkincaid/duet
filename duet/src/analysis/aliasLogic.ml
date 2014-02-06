(*pp camlp4find deriving.syntax *)

(** Interprocedural dependence analysis with support for pointers. *)
open Core
open CfgIr
open EqLogic
open Apak
open Expr

module DG = Afg.G
module Pack = Afg.Pack

(** Track must-alias relationships *)
let must_alias = ref true

let concurrent = ref false

let _ =
  CmdLine.register_config
    ("-no-must-alias", Arg.Clear must_alias, " Disable must-alias information")
let _ =
  CmdLine.register_config
    ("-concurrent", Arg.Set concurrent, " Perform concurrent dependence analysis")

module RG = Interproc.RG

module type SegmentAnalysis = sig
  type summary
  type left_summary
  type right_summary

  val name : string
  val weight : def -> summary

  val lower_left : left_summary -> summary
  val lower_right : right_summary -> summary

  val left_weight : def -> left_summary
  val right_weight : def -> right_summary

  val left_action : summary -> left_summary -> left_summary
  val right_action : summary -> right_summary -> right_summary
end

module MakeSegment
  (L : Sig.KA.Quantified.Ordered.S with type var = var)
  (K : Sig.KA.Quantified.Ordered.S with type var = var)
  (R : Sig.KA.Quantified.Ordered.S with type var = var)
  (A : SegmentAnalysis with type summary = K.t
		       and type left_summary = L.t
		       and type right_summary = R.t) =
struct

  module Acc(K : Sig.KA.Quantified.Ordered.S) = struct
    include K
    let widen = K.add
  end
  module Left = Interproc.MakePathExpr(Acc(L))
  module IntraLeft = Pathexp.MakeElim(RG.G)(Acc(L))
  module Right = Pathexp.MakeElim(RG.G)(Acc(R))

  (** Iterate over the solution to the analysis.  An item in the solution
      consists of a program point (definition) along with a summary of the set
      of (interprocedurally valid) paths to that that point.  *)
  let solve smash file init =
    let rg = Interproc.make_recgraph file in
    let main = match file.entry_points with
      | [x] -> x
      | _   -> failwith "Interproc.solve: No support for multiple entry points"
    in
    let local f =
      let cf = lookup_function f file in
      fun x -> is_local cf (fst x) || is_formal cf (fst x)
    in
    let left_query = Left.mk_query rg A.left_weight local main in
    let go (_, v, path_to_v) = smash path_to_v (A.right_weight v) in
    BatEnum.iter go (Left.enum_single_src left_query)
end

module MakeSegmentConc
  (L : Sig.KA.Quantified.Ordered.S with type var = var)
  (K : Sig.KA.Quantified.Ordered.S with type var = var)
  (R : Sig.KA.Quantified.Ordered.S with type var = var)
  (A : SegmentAnalysis with type summary = K.t
		       and type left_summary = L.t
		       and type right_summary = R.t) =
struct

  module Acc(K : Sig.KA.Quantified.Ordered.S) = struct
    include K
    let widen = K.add
  end
  module Left = Interproc.MakePathExpr(Acc(L))
  module IntraLeft = Pathexp.MakeElim(RG.G)(Acc(L))
  module Right = Pathexp.MakeElim(RG.G)(Acc(R))

  (** Iterate over the solution to the analysis.  An item in the solution
      consists of a program point (definition) along with a summary of the set
      of (interprocedurally valid) paths to that that point.  *)
  let solve smash file init =
    let rg = Interproc.make_recgraph file in
    let main = match file.entry_points with
      | [x] -> x
      | _   -> failwith "Interproc.solve: No support for multiple entry points"
    in
    let local f =
      let cf = lookup_function f file in
      fun x -> is_local cf (fst x) || is_formal cf (fst x)
    in
    (* Adds edges to the callgraph for each fork. Shouldn't really have to do
     * this every time a new query is made *)
    let add_fork_edges q =
      let f (b, v) = match v.dkind with
        | Builtin (Fork (vo, e, elst)) -> Left.add_callgraph_edge q b (LockLogic.get_func e)
        | _ -> ()
      in
        BatEnum.iter f (Interproc.RG.vertices rg)
    in
    let classify v = match v.dkind with
      | Builtin (Fork (vo, e, elst)) -> RecGraph.Block (LockLogic.get_func e)
      | _ -> Interproc.V.classify v
    in
    let left_query = Left.mk_query rg A.left_weight local main in
    let go (_, v, path_to_v) = smash path_to_v (A.right_weight v) in
      add_fork_edges left_query;
      BatEnum.iter go (Left.enum_single_src_tmp classify left_query)
end

(* The dependence analysis is parameterized over a ConjFormula functor (which
   is expected to be either EqLogic.Hashed.MakeEQ or
   EqLogic.Hashed.MakeTrivEQ.  This lets us play around with the precision of
   the must-alias analysis (and in particular, is used to implement the
   -no-must-alias command line option) *)
module Make(MakeEQ :
	      functor (P : Hashed.Predicate with type var = Var.t) ->
		Hashed.ConjFormula with type var = Var.t
				   and type pred = P.t) =
struct

  (* Kill predicate.  We can think of KillFormula = MakeEq(KillPred) as
     formulae equality logic formulae with a unary predicate symbol K which
     represents access paths that have been killed along a path.  *)
  module KillPred = struct
    type t = AP.Set.t deriving (Show,Compare)
    type var = Var.t
    let compare = Compare_t.compare
    let format = Show_t.format
    let show = Show_t.show

    let equal = AP.Set.equal
    let unit = AP.Set.empty
    let mul = AP.Set.union
    let subst sub_var set =
      let add iap set = match AP.psubst_var sub_var iap with
	| Some z -> AP.Set.add z set
	| None   -> set
      in
      AP.Set.fold add set AP.Set.empty
    let hash = AP.Set.hash
    let implies sub x y =
      let sub_iap iap =
	match AP.psubst_var (fun x -> Some (sub x)) iap with
	| Some z -> z
	| None -> assert false (* impossible *)
      in
	AP.Set.for_all (fun k -> AP.Set.mem (sub_iap k) x) y
  end

  module KillMinterm = MakeEQ(KillPred)
  module KillFormula = MakeFormula(KillMinterm)
  module KillTransition = KillFormula.Transition
  module KillState = KillFormula.State

  (* Reaching definition predicate. *)
  type rd_pred = {
    current_name : ap option; (* If ap is accessible, the indexed access path
				 that accesses it; None otherwise. *)
    killed : AP.Set.t; (* Accessible access paths that have been killed
			  between the definition point and the end of the
			  path *)
  }
    deriving (Show,Compare)

  module RDPred = struct
    type t = rd_pred deriving (Show,Compare)
    type var = Var.t
    let format = Show_t.format
    let show = Show_t.show
    let compare = Compare_t.compare
    let equal x y = compare x y = 0

    let hash x =
      Hashtbl.hash
	[(match x.current_name with Some ap -> AP.hash ap | None -> 0);
	 AP.Set.hash x.killed]

    (* True *)
    let unit = { current_name = None; killed = AP.Set.empty }

    (* Conjunction *)
    let mul x y =
      let current_name = match x.current_name, y.current_name with
	| (None, x) | (x, _) -> x
      in
      { current_name = current_name;
	killed = AP.Set.union x.killed y.killed }

    let subst subst_var x =
      let current = match x.current_name with
	| Some name -> AP.psubst_var subst_var name
	| None -> None
      in
      { current_name = current;
	killed = KillPred.subst subst_var x.killed }

    let implies sub x y =
      let sub_ap ap =
	match AP.psubst_var (fun x -> Some (sub x)) ap with
	| Some z -> z
	| None -> assert false (* impossible *)
      in
      let in_x k = AP.Set.mem (sub_ap k) x.killed in
	match x.current_name, y.current_name with
	  | (None, None) -> AP.Set.for_all in_x y.killed
	  | (Some xname, Some yname) ->
	      AP.equal xname yname && AP.Set.for_all in_x y.killed
	  | _ -> false
  end

  module RDMinterm = MakeEQ(RDPred)
  module RDFormula = MakeFormula(RDMinterm)
  module RDTransition = RDFormula.Transition
  module RDState = RDFormula.State

  module DefAP = struct
    type t = Def.t * AP.t
      deriving (Show, Compare)
    let format = Show_t.format
    let show = Show_t.show
    let compare = Compare_t.compare
    let hash (def, ap) = Hashtbl.hash (Def.hash def, AP.hash ap)
    let equal x y = compare x y = 0
  end

  module RDMap =
    Monoid.FunctionSpace.Total.Ordered.Make
      (DefAP)
      (Ka.Ordered.AdditiveMonoid(RDTransition))

  module VarRDMap =
    Monoid.FunctionSpace.Total.Ordered.Make
      (Var)
      (Semilattice.Bounded.Ordered.Monoid(Lattice.LiftSubset(Def.Set)))

  module DefAPSet = Putil.Hashed.Set.Make(DefAP)
  module DefAPSetHT = Hashtbl.Make(DefAPSet)

  (****************************************************************************)
  (* Join / split vertices                                                    *)
  (****************************************************************************)
  let join_ht = DefAPSetHT.create 1024
  let join_reverse_ht = Def.HT.create 1024
  let make_join set =
    try DefAPSetHT.find join_ht set
    with Not_found ->
      let def = Def.mk (Assume Bexpr.ktrue) in
      let ap = snd (DefAPSet.choose set) in (* This choice does not matter *)
      let def_ap = (def, ap) in
	DefAPSetHT.add join_ht set def_ap;
	Def.HT.add join_reverse_ht def set;
	def_ap

  let make_var_join var set =
    let def_ap_set =
      let var = Variable var in
      let add d s = DefAPSet.add (d, var) s in
	Def.Set.fold add set DefAPSet.empty
    in
      Def.Set.singleton (fst (make_join def_ap_set))

  (* Since assume(true) doesn't define anything, if assume(true) is ever a
     reaching definition, we know that it's a join node *)
  let is_join def = match def.dkind with
    | Assume bexpr -> Bexpr.equal bexpr Bexpr.ktrue
    | _            -> false
  let lookup_join def =
    try Def.HT.find join_reverse_ht def
    with Not_found -> assert false

  (* Split vertices ***********************************************************)
  let split_ht = DefAPSetHT.create 1024
  let split_reverse_ht = Def.HT.create 1024
  let make_split set =
    try DefAPSetHT.find split_ht set
    with Not_found ->
      let def = Def.mk (Assume Bexpr.ktrue) in
      let ap = snd (DefAPSet.choose set) in (* This choice does not matter *)
      let def_ap = (def, ap) in
	DefAPSetHT.add split_ht set def_ap;
	Def.HT.add split_reverse_ht def set;
	def_ap
  let make_var_split var set =
    let def_ap_set =
      let var = Variable var in
      let add d s = DefAPSet.add (d, var) s in
	Def.Set.fold add set DefAPSet.empty
    in
      Def.Set.singleton (fst (make_split def_ap_set))
  let lookup_join def =
    try Def.HT.find join_reverse_ht def
    with Not_found -> assert false

  (* Since assume(true) doesn't define anything, if assume(true) is ever a
     reaching definition, we know that it's a split node *)
  let is_split def = match def.dkind with
    | Assume bexpr -> Bexpr.equal bexpr Bexpr.ktrue
    | _            -> false
  let lookup_split def =
    try Def.HT.find split_reverse_ht def
    with Not_found -> assert false
  (****************************************************************************)


  module MemTR = struct
    type t = Pa.MemLoc.Set.t * RDTransition.t
      deriving (Show,Compare)
    let format = Show_t.format
    let show = Show_t.show
    let compare = Compare_t.compare
  end
  module ReverseRDMap =
    Monoid.FunctionSpace.Total.Make
      (MemTR)
      (Semilattice.Bounded.Monoid(Lattice.LiftSubset(DefAPSet)))

  (* Lift a KillTransition to an RDTransition *)
  let lift_kill_transition kill_tr =
    let frame = KillTransition.get_frame kill_tr in
    let f minterm rest =
      let killed = KillMinterm.get_pred minterm in
      let eqs = KillMinterm.get_eqs minterm in
      let pred =
	{ current_name = None;
	  killed = killed }
      in
      let new_minterm = RDMinterm.make eqs pred in
      let new_tr = RDTransition.of_minterm frame new_minterm in
      RDTransition.add new_tr rest
    in
    KillTransition.fold_minterms f kill_tr RDTransition.zero

  (* Lift a KillTransition to an RDTransition, but forget about the killed
     access paths *)
  let lift_kill_transition_eq kill_tr =
    let frame = KillTransition.get_frame kill_tr in
    let f minterm rest =
      let eqs = KillMinterm.get_eqs minterm in
      let pred =
	{ current_name = None;
	  killed = AP.Set.empty }
      in
      let new_minterm = RDMinterm.make eqs pred in
      let new_tr = RDTransition.of_minterm frame new_minterm in
      RDTransition.add new_tr rest
    in
    KillTransition.fold_minterms f kill_tr RDTransition.zero

  (* Remove dead definitions (definitions of memory locations which are
     overwritten later in the path) *)
  let filter_rd rd_tr =
    let frame = RDTransition.get_frame rd_tr in
    let f minterm rest =
      let pred = RDMinterm.get_pred minterm in
      let add = match pred.current_name with
	| Some name -> not (AP.Set.mem name pred.killed)
	| None -> true
      in
      if add
      then RDTransition.add (RDTransition.of_minterm frame minterm) rest
      else rest
    in
    RDTransition.fold_minterms f rd_tr RDTransition.zero

  (* Abstract paths *)
  type abspath = { kill_tr : KillTransition.t;
		   kill_var : Var.Set.t option }
    deriving (Show,Compare)
  module AbsPath = struct
    type t = abspath deriving (Show,Compare)
    type var = Core.var
    let compare = Compare_t.compare
    let format = Show_t.format
    let show = Show_t.show
    let equal x y = compare x y = 0
    let zero =
      { kill_tr = KillTransition.zero;
	kill_var = None }
    let one =
      { kill_tr = KillTransition.one;
	kill_var = Some (Var.Set.empty) }
    let lower = function
      | Some x -> x
      | None -> Var.Set.empty
    let mul x y =
      let kill_var = match x.kill_var, y.kill_var with
	| (Some k0, Some k1) -> Some (Var.Set.union k0 k1)
	| (_, _) -> None
      in
      { kill_tr = KillTransition.mul x.kill_tr y.kill_tr;
	kill_var = kill_var }
    let add x y =
      let kill_var = match x.kill_var, y.kill_var with
	| (Some k0, Some k1) -> Some (Var.Set.inter k0 k1)
	| (None, x) | (x, None) -> x
      in
      { kill_tr = KillTransition.add x.kill_tr y.kill_tr;
	kill_var = kill_var }
    let star x =
      { kill_tr = KillTransition.star x.kill_tr;
	kill_var = Some Var.Set.empty }
    let exists p x =
      let kill_var = match x.kill_var with
	| Some x -> Some (Var.Set.filter p x)
	| None -> None
      in
      { kill_tr = KillTransition.exists p x.kill_tr;
	kill_var = kill_var }
    let get_frame x = KillTransition.get_frame x.kill_tr
  end

  let lower = function
    | Some x -> x
    | None -> Var.Set.empty

  type rd = { reaching_defs : RDMap.t;
	      reaching_lvl0 : VarRDMap.t;
	      abspath : AbsPath.t }
    deriving (Show,Compare)

  module RD = struct
    type t = rd deriving (Show,Compare)
    type var = Core.var

    let format = Show_t.format
    let show = Show_t.show
    let compare = Compare_t.compare

    let get_frame x = AbsPath.get_frame x.abspath

    (* Join nodes lead to non-monotonicity for recursive functions, so
       comparison & equality testing require expanding join nodes first.  *)
    let expand_rdmap map =
      let rec add map ((def,ap), tr) =
	if is_join def
	then DefAPSet.fold (fun da map -> add map (da,tr)) (lookup_join def) map
	else RDMap.update (def,ap) tr map
      in
      BatEnum.fold add RDMap.unit (RDMap.enum map)

    let expand_varmap map =
      let rec add def set =
	let f (def,_) set = add def set in
	if is_join def then DefAPSet.fold f (lookup_join def) set
	else Def.Set.add def set
      in
      let f defs = Def.Set.fold add defs Def.Set.empty in
      VarRDMap.map f map
    let canonicalize x = {x with
			    reaching_defs = expand_rdmap x.reaching_defs;
			    reaching_lvl0 = expand_varmap x.reaching_lvl0 }

    let equal x y = compare x y = 0

    let zero =
      { abspath = AbsPath.zero;
	reaching_defs = RDMap.unit;
	reaching_lvl0 = VarRDMap.unit }
    let one =
      { abspath = AbsPath.one;
	reaching_defs = RDMap.unit;
	reaching_lvl0 = VarRDMap.unit }

    let reverse rd =
      let open ReverseRDMap in
      let f ((def,ap), tr) =
	update
	  (Pa.resolve_ap ap, tr)
	  (DefAPSet.singleton (def,ap))
	  unit
      in
      BatEnum.fold mul unit (BatEnum.map f (RDMap.enum rd))

    let mk_joins x =
      let add map ((_, tr), rd) =
	if DefAPSet.cardinal rd > 1 then RDMap.update (make_join rd) tr map
	else RDMap.update (DefAPSet.choose rd) tr map
      in
      let reaching_defs =
	BatEnum.fold
	  add
	  RDMap.unit
	  (ReverseRDMap.enum (reverse x.reaching_defs))
      in
      let join_var m (v, defs) =
	if Def.Set.cardinal defs > 1
	then VarRDMap.update v (make_var_join v defs) m
	else m
      in
      let reaching_lvl0 =
	BatEnum.fold join_var x.reaching_lvl0 (VarRDMap.enum x.reaching_lvl0)
      in
      { x with
	reaching_defs = reaching_defs;
	reaching_lvl0 = reaching_lvl0 }

    let update_reaching reaching abspath =
      let kill = lift_kill_transition abspath.kill_tr in
      let update_rd kill_tr = filter_rd (RDTransition.mul kill_tr kill) in
      RDMap.map update_rd reaching

    let update_reaching_left reaching abspath =
      let eqs = lift_kill_transition_eq abspath.kill_tr in
      let update_rd kill_tr = filter_rd (RDTransition.mul eqs kill_tr) in
      RDMap.map update_rd reaching

    let mul x y =
      if equal x zero || equal y zero then zero else begin
	let abspath = AbsPath.mul x.abspath y.abspath in
	let x_reaching =
	  update_reaching x.reaching_defs y.abspath
	in
	let y_reaching =
	  update_reaching_left y.reaching_defs x.abspath
	in
	let x_lvl0_reaching = match y.abspath.kill_var with
	  | Some y_killed ->
	    Var.Set.fold
	      (fun v reaching -> VarRDMap.update v Def.Set.empty reaching)
	      y_killed
	      x.reaching_lvl0
	  | None -> VarRDMap.unit
	in
	  { abspath = abspath;
	    reaching_defs = RDMap.mul x_reaching y_reaching;
	    reaching_lvl0 = VarRDMap.mul x_lvl0_reaching y.reaching_lvl0 }
      end

    let add x y =
      { abspath = AbsPath.add x.abspath y.abspath;
	reaching_defs = RDMap.mul x.reaching_defs y.reaching_defs;
	reaching_lvl0 = VarRDMap.mul x.reaching_lvl0 y.reaching_lvl0 }

    let star x =
      let abspath = AbsPath.star x.abspath in
      let reaching = update_reaching x.reaching_defs abspath in
      let reaching = update_reaching_left reaching abspath in
	{ abspath = abspath;
	  reaching_defs = reaching;
	  reaching_lvl0 = x.reaching_lvl0 }

    let exists p x =
      let add_reach reach ((def, ap), rd_tr) =
	let add = match ap with
	  | Variable v -> p v
	  | _ -> true
	in
	  if add then RDMap.update (def, ap) (RDTransition.exists p rd_tr) reach
	  else reach
      in
      let reaching_lvl0 =
	let remove_rd m var =
	  if p var then m else VarRDMap.update var Def.Set.empty m
	in
	BatEnum.fold
	  remove_rd
	  x.reaching_lvl0
	  (VarRDMap.support x.reaching_lvl0)
      in
      let reaching_defs =
	BatEnum.fold add_reach RDMap.unit (RDMap.enum x.reaching_defs)
      in
	mk_joins
	  { abspath = AbsPath.exists p x.abspath;
	    reaching_defs = reaching_defs;
	    reaching_lvl0 = reaching_lvl0 }
  end

  module EUMap = RDMap
  module VarEUMap = VarRDMap
  module EU = struct
    type t =
	{ exposed_uses : EUMap.t;
	  exposed_var_uses : VarEUMap.t;
	  abspath : AbsPath.t }
	  deriving (Show, Compare)
    type var = Core.var
    let compare = Compare_t.compare
    let format = Show_t.format
    let show = Show_t.show
    let equal x y = compare x y = 0
    let zero =
      { abspath = AbsPath.zero;
	exposed_uses = EUMap.unit;
	exposed_var_uses = VarEUMap.unit }
    let one =
      { abspath = AbsPath.one;
	exposed_uses = EUMap.unit;
	exposed_var_uses = VarEUMap.unit }
    let add x y =
      { abspath = AbsPath.add x.abspath y.abspath;
	exposed_uses = EUMap.mul x.exposed_uses y.exposed_uses;
	exposed_var_uses = VarEUMap.mul x.exposed_var_uses y.exposed_var_uses }

    let update_uses uses abspath =
      let kill = lift_kill_transition abspath.kill_tr in
      let update_use kill_tr = filter_rd (RDTransition.mul kill kill_tr) in
      EUMap.map update_use uses

    let mul x y =
      (* zero is a multiplicative annihiliator on the left, but not the
	 right! *)
      (*    if equal x zero || equal y zero then zero else *)begin
      let abspath = AbsPath.mul x.abspath y.abspath in
      let y_uses = update_uses y.exposed_uses x.abspath in
      let y_var_uses = match x.abspath.kill_var with
	| Some x_killed ->
	    Var.Set.fold
	      (fun v reaching -> VarRDMap.update v Def.Set.empty reaching)
	      x_killed
	      y.exposed_var_uses
	| None -> VarEUMap.unit
      in
	{ abspath = abspath;
	  exposed_uses = EUMap.mul x.exposed_uses y_uses;
	  exposed_var_uses = VarEUMap.mul x.exposed_var_uses y_var_uses }
    end

    let star x =
      let abspath = AbsPath.star x.abspath in
	{ abspath = abspath;
	  exposed_uses = update_uses x.exposed_uses abspath;
	  exposed_var_uses = x.exposed_var_uses }

    let reverse rd =
      let open ReverseRDMap in
      let f ((def,ap), tr) =
	update
	  (Pa.resolve_ap ap, tr)
	  (DefAPSet.singleton (def,ap))
	  unit
      in
      BatEnum.fold mul unit (BatEnum.map f (RDMap.enum rd))

    let mk_splits x =
      let add map ((_, tr), rd) =
	if DefAPSet.cardinal rd > 1 then EUMap.update (make_split rd) tr map
	else EUMap.update (DefAPSet.choose rd) tr map
      in
      let exposed_uses =
	BatEnum.fold
	  add
	  EUMap.unit
	  (ReverseRDMap.enum (reverse x.exposed_uses))
      in
      let split_var m (v, defs) =
	if Def.Set.cardinal defs > 1
	then VarEUMap.update v (make_var_split v defs) m
	else m
      in
      let exposed_var_uses =
	BatEnum.fold
	  split_var
	  x.exposed_var_uses
	  (VarRDMap.enum x.exposed_var_uses)
      in
	{ x with
	    exposed_uses = exposed_uses;
	    exposed_var_uses = exposed_var_uses }

    let exists p x =
      let add_use uses ((def, ap), rd_tr) =
	let add = match ap with
	  | Variable v -> p v
	  | _ -> true
	in
	  if add then EUMap.update (def, ap) (RDTransition.exists p rd_tr) uses
	  else uses
      in
	{ abspath = AbsPath.exists p x.abspath;
	  exposed_uses =
	    BatEnum.fold add_use EUMap.unit (EUMap.enum x.exposed_uses);

	  (* Uses of existentially quantified variables still need to be
	     propagated so that they will get a reaching definition from the
	     uninit location.  We could also probably just create the edges
	     here instead to avoid this. *)
	  exposed_var_uses = x.exposed_var_uses }

  end

  module ReachingDefs = struct
    type left_summary = RD.t
    type right_summary = EU.t
    type summary = AbsPath.t
    let name = "Dependence analysis"

    let generalize = AbsPath.exists
    let generalize_ctx _ () = ()

    let assign_abspath lhs rhs =
      match lhs with
	| Variable v ->
	    { kill_var = Some (Var.Set.singleton v);
	      kill_tr = KillTransition.assign lhs rhs AP.Set.empty }
	| _ ->
	    let killed = AP.Set.singleton (AP.subscript 0 lhs) in
	      { kill_var = Some Var.Set.empty;
		kill_tr = KillTransition.assign lhs rhs killed }

    let assume_abspath bexpr =
      let uses = Bexpr.get_uses bexpr in
      let (killed, kill_var) =
	let f ap (killed, kill_var) = match ap with
	  | Variable v ->
	      (killed, Var.Set.add v kill_var)
	  | _ ->
	      (AP.Set.add (AP.subscript 0 ap) killed, kill_var)
	in
	  AP.Set.fold f uses (AP.Set.empty, Var.Set.empty)
      in
      let frame =
	let add ap set =
	  Var.Set.union (AP.free_vars (AP.unsubscript ap)) set
	in
	  AP.Set.fold add killed Var.Set.empty
      in
      let kill_tr = KillTransition.assume bexpr frame killed in
	{ kill_var = Some kill_var;
	  kill_tr = kill_tr }

    let assign_weight def lhs rhs =
      match lhs with
	| Variable v ->
	    { reaching_defs = RDMap.unit;
	      abspath = assign_abspath lhs rhs;
	      reaching_lvl0 =
		VarRDMap.update v (Def.Set.singleton def) VarRDMap.unit }
	| _ ->
	    let rd_pred =
	      { current_name = Some (AP.subscript 0 lhs);
		killed = AP.Set.empty }
	    in
	    let rd_tr = RDTransition.assign lhs rhs rd_pred in
	    let reaching_defs = RDMap.update (def, lhs) rd_tr RDMap.unit in
	      { reaching_defs = reaching_defs;
		abspath = assign_abspath lhs rhs;
		reaching_lvl0 = VarRDMap.unit }

    let assume_weight def bexpr =
      let uses = Bexpr.get_uses bexpr in
      let add_rd use reaching =
	let rd_pred =
	  { current_name = Some (AP.subscript 0 use);
	    killed = AP.Set.empty }
	in
	let rd_tr = RDTransition.assume bexpr (AP.free_vars use) rd_pred in
	  RDMap.update (def, use) rd_tr reaching
      in
      let (killed, kill_lvl0, rd, rdlvl0) =
	let f ap (killed, lvl0, rd, rdlvl0) = match ap with
	  | Variable v ->
	      (killed, Var.Set.add v lvl0, rd,
	       VarRDMap.update v (Def.Set.singleton def) rdlvl0)
	  | _ ->
	      (AP.Set.add (AP.subscript 0 ap) killed, lvl0, add_rd ap rd, rdlvl0)
	in
	let init = (AP.Set.empty, Var.Set.empty, RDMap.unit, VarRDMap.unit) in
	  AP.Set.fold f uses init
      in
	{ reaching_defs = rd;
	  abspath = assume_abspath bexpr;
	  reaching_lvl0 = rdlvl0 }

    let assign_string_const def lhs rhs =
      let tr = assign_weight def lhs rhs in
      let ap = AP.offset (Deref (AccessPath lhs)) OffsetUnknown in
      let rd_pred =
	{ current_name = Some (AP.subscript 1 ap);
	  killed = AP.Set.empty }
      in
      let rd_tr =
	RDTransition.assign lhs (Havoc (AP.get_type ap)) rd_pred
      in
      let reaching_defs =
	RDMap.update (Def.initial, ap) rd_tr tr.reaching_defs
      in
      { tr with reaching_defs = reaching_defs }

    let left_weight def = match def.dkind with
      | Assign (lhs, rhs) -> begin
	let lhs = Variable lhs in
	match strip_casts rhs with
	| Constant (CString str) -> assign_string_const def lhs rhs
	| _ -> assign_weight def lhs rhs
      end
      | Store (lhs, rhs) -> begin
	match strip_casts rhs with
	| Constant (CString str) -> assign_string_const def lhs rhs
	| _ -> assign_weight def lhs rhs
      end
      | Assume exp | Assert (exp, _) -> assume_weight def exp
      | AssertMemSafe (expr, _) ->
	  assume_weight def (Bexpr.of_expr expr)
      | Call (_, _, _) -> RD.one
      | Return _ -> assert false
(*
      | Return (Some expr) ->
	  let return_ap = Variable (Var.mk (return_var func.fname)) in
	    assign_weight def return_ap expr
*)
      | Builtin (Alloc (lhs, size, _)) ->
	  let tr =
	    assign_weight def (Variable lhs) (Havoc (Var.get_type lhs))
	  in
	  let add_rd offset reaching =
	    let ap = AP.offset (Deref (AccessPath (Variable lhs))) offset in
	    let rd_pred =
	      { current_name = Some (AP.subscript 1 ap);
		killed = AP.Set.empty }
	    in
	    let rd_tr =
	      RDTransition.assign
		(Variable lhs)
		(Havoc (AP.get_type ap))
		rd_pred
	    in
	      RDMap.update (Def.initial, ap) rd_tr reaching
	  in
	  let reaching_defs =
	    match Expr.simplify size with
	      | Constant (CInt (ksize, _)) ->
		  let f reaching i = add_rd (OffsetFixed i) reaching in
		    BatEnum.fold f tr.reaching_defs (BatInt.(--) 0 (ksize-1))
	      | _ -> add_rd OffsetUnknown tr.reaching_defs
	  in
	    { tr with reaching_defs = reaching_defs }
      | Builtin Exit -> RD.zero
      | _ -> RD.one

    let weight def = match def.dkind with
      | Store (lhs, rhs) -> assign_abspath lhs rhs
      | Assign (lhs, rhs) -> assign_abspath (Variable lhs) rhs
      | Assume exp | Assert (exp, _) -> assume_abspath exp
      | AssertMemSafe (expr, _) -> assume_abspath (Bexpr.of_expr expr)
      | Builtin (Alloc (lhs, _, _)) ->
	assign_abspath (Variable lhs) (Havoc (Var.get_type lhs))
      | Builtin Exit -> AbsPath.zero
      | Return _ -> assert false
(*
      | Return (Some expr) ->
	  assign_abspath (Variable (Var.mk (return_var func.fname))) expr
*)
      | Call (_, _, _) -> assert false
      | _ -> AbsPath.one

    let right_weight def =
      let (uses, var_uses) =
	let add ap (uses, var_uses) = match ap with
	  | Deref _ ->
	    let rd_pred =
	      { current_name = Some (AP.subscript 0 ap);
		killed = AP.Set.empty }
	    in
	    let rd_tr =
	      RDTransition.assume
		Bexpr.ktrue
		(AP.free_vars ap)
		rd_pred
	    in
	    let uses = EUMap.update (def, ap) rd_tr uses in
	    (uses, var_uses)
	  | Variable v ->
	    (uses, VarEUMap.update v (Def.Set.singleton def) var_uses)
	in
	AP.Set.fold add (Def.get_uses def) (EUMap.unit, VarEUMap.unit)
      in
      let abspath =
	match def.dkind with
	| Call (_, _, _) -> AbsPath.one
	| _ -> weight def
      in
      { EU.abspath = abspath;
	EU.exposed_uses = uses;
	EU.exposed_var_uses = var_uses }

    let lower_right x = x.EU.abspath
    let lower_left x = x.abspath
    let promote_left x =
      { abspath = x;
	reaching_defs = RDMap.unit;
	reaching_lvl0 = VarRDMap.unit }
    let promote_right x =
      { EU.abspath = x;
	EU.exposed_uses = EUMap.unit;
	EU.exposed_var_uses = VarEUMap.unit }

    let right_action abspath uses = EU.mul (promote_right abspath) uses
    let left_action abspath reaching = RD.mul (promote_left abspath) reaching
  end
  module ReachingDefsConc = struct
    include ReachingDefs
    let stabilize x def = 
      let a = x.kill_tr in
      let races = LockLogic.get_races () in
      let pre =
        let frame = try Def.HT.find races def with Not_found -> Var.Set.empty in
          KillTransition.of_minterm frame (KillMinterm.unit)
      in
      let post =
        let frame = try Def.HT.find races def with Not_found -> Var.Set.empty in
          KillTransition.of_minterm frame (KillMinterm.unit)
      in
        { x with kill_tr = KillTransition.mul pre (KillTransition.mul a post) }

    let left_weight def = 
      let x = ReachingDefs.left_weight def in
        { x with abspath = stabilize x.abspath def }
    let right_weight def = 
      let x = ReachingDefs.right_weight def in
        { x with EU.abspath = stabilize x.EU.abspath def }
    let weight def = 
      let x = ReachingDefs.weight def in
        stabilize x def
  end
  module RDAnalysis = MakeSegment(RD)(AbsPath)(EU)(ReachingDefs)
  module RDAnalysisConc = MakeSegmentConc(RD)(AbsPath)(EU)(ReachingDefsConc)

  let get_current_name minterm = (RDMinterm.get_pred minterm).current_name
  let incr_index =
    RDMinterm.subst (fun x -> Var.subscript x (Var.get_subscript x + 1))

  (* Determine whether an access path has been killed along the path formed by
     catenating the two paths left and right *)
  let killed_on_composition left right =
    let path =
      RDMinterm.exists
	(fun _ -> true)
	(RDMinterm.mul left right)
    in
    let subst = RDMinterm.get_subst path in
    let killed = (RDMinterm.get_pred path).killed in
      (fun ap -> AP.Set.mem (AP.subst_var subst ap) killed)

  (* Determine whether there exists a minterm d of def_tr and u of use_tr such
     that f d u holds *)
  let exists_du f def_tr use_tr =
    let add_du_minterm def_path use_path exists =
      exists || (f def_path use_path)
    in
    let add_def_minterm def_path exists =
      exists
        || RDTransition.fold_minterms (add_du_minterm def_path) use_tr false
    in
      RDTransition.fold_minterms add_def_minterm def_tr false

  let construct_dg file =
    let dg = DG.create () in
    let add_edge def (def_ap, use_ap) use =
      Log.debugf "Add edge %a -> %a"
	Def.format def
	Def.format use;
      DG.add_edge_e
	dg
	(DG.E.create
	   def
	   (Pack.PairSet.singleton (Pack.mk_pair def_ap use_ap))
	   use)
    in

    (* Given a set of reaching definitions (left) and a set of upwards exposed
       uses (right) to a point p, add the edges corresponding to reaching
       definitions through p. *)
    let smash left right =
      let reaching_defs = left.reaching_defs in
      let reaching_lvl0 = left.reaching_lvl0 in
      let var_killed = match left.abspath.kill_var with
	| Some x -> (fun v -> Var.Set.mem v x)
	| None -> (fun v -> true)
      in
      let exposed_uses = right.EU.exposed_uses in
      let exposed_lvl0 = right.EU.exposed_var_uses in

      (* Determine whether an edge should be added between a particular
	 reaching definition and exposed use, and add it if there should
	 be. *)
      let add_rd_eu ((def,def_ap), def_tr) ((use,use_ap), use_tr) =
        if Pa.may_alias def_ap use_ap then begin
          let f def_path use_path =
            match get_current_name def_path, get_current_name use_path with
              | (None, None) -> true
              | _ -> begin
                  let use_path = incr_index use_path in

                  let killed = killed_on_composition def_path use_path in
                  let killed_current path =
                    match get_current_name path with
                      | Some ap -> killed ap
                      | None -> false
                  in
                    not (killed_current use_path || killed_current def_path)
                end
          in
            if exists_du f def_tr use_tr then add_edge def (def_ap, use_ap) use
        end
      in

      (* For a given exposed use, add all the edges with a source that is a
	 write to a variable that use_ap may point to. *)
      let add_eu_var_def (use,use_ap) =
	let add_var_defs = function
	  | (Pa.MAddr v,offset) -> begin
	    let defs = VarRDMap.eval reaching_lvl0 (v, offset) in
	    let var_ap = Variable (v, offset) in
	    let add_edge_to_eu def = add_edge def (var_ap, use_ap) use in
	    Def.Set.iter add_edge_to_eu defs;
	    if not (var_killed (v, offset))
	    then add_edge Def.initial (var_ap, use_ap) use
	  end
	  | _ -> ()
	in
	Pa.MemLoc.Set.iter add_var_defs (Pa.resolve_ap use_ap)
      in

      let add_rd rd =
	BatEnum.iter (fun eu -> add_rd_eu rd eu) (EUMap.enum exposed_uses)
      in

      (* Add reaching definitions for upward-exposed variable uses *)
      let add_rd_var (v, uses) =
	let defs = VarRDMap.eval reaching_lvl0 v in
	let add_mem_var_edges (def,ap) =
	  if Pa.may_alias ap (Variable v)
	  then Def.Set.iter (fun u -> add_edge def (ap, Variable v) u) uses
	in
	let add_edge d u = add_edge d (Variable v, Variable v) u in
	Def.Set.iter (fun d -> Def.Set.iter (add_edge d) uses) defs;
	if not (var_killed v)
	then Def.Set.iter (add_edge Def.initial) uses;
	BatEnum.iter add_mem_var_edges (RDMap.support reaching_defs)
      in
      Log.debug "-----   SMASH   -----";
      Log.debug_pp RD.format left;
      Log.debug_pp EU.format right;
      BatEnum.iter add_rd (RDMap.enum reaching_defs);
      BatEnum.iter add_rd_var (VarEUMap.enum exposed_lvl0);
      BatEnum.iter add_eu_var_def (EUMap.support exposed_uses);
      Log.debug "----- END SMASH -----"
    in
    let smash left right = Log.time "smash" (smash left) right in
    let add_join_edge set (join,y) =
      DefAPSet.iter (fun (d,x) -> add_edge d (x,y) join) set
    in
    DefAPSetHT.clear join_ht;
    Log.phase "Dependence analysis" ((if !concurrent then RDAnalysisConc.solve 
                                                     else RDAnalysis.solve)
                                       smash file) ();
    DefAPSetHT.iter add_join_edge join_ht;
    Dg.simplify_dg dg;
    if !CmdLine.sanity_checks then DG.sanity_check dg;
    if !CmdLine.display_graphs then DG.display_labelled dg;
    dg
end

open Ai
type typ = Oct.t
let man = Oct.manager_alloc ()(*Box.manager_alloc ()*)

let predicates aps =
  let add ap set =
    if is_pointer_type (AP.get_type ap)
    then Exponential.PSet.add (Bexpr.ge (AccessPath ap) Expr.one) set
    else set
  in
    AP.Set.fold add aps Exponential.PSet.empty

module ApronI =
  Exponential.Make(struct
    type t = typ
    let man = man
    let predicates = predicates
  end)
module I = IExtra(ApronI)

module IntervalAnalysis = Solve.MakeAfgSolver(I)

module Dep = Make(EqLogic.Hashed.MakeEQ(Var))
module TrivDep = Make(EqLogic.Hashed.MakeTrivEQ(Var))

let construct_dg file =
  ignore (Bddpa.initialize file);
  Pa.simplify_calls file;
  if !must_alias then Dep.construct_dg file
  else TrivDep.construct_dg file

let interval_analysis file =
  let changed = ref false in
  let remove_unreachable dg map file =
    let process_func func =
      let remove_vertex v =
	match v.dkind with
	  | Assume _ ->
	      if (DG.mem_vertex dg v
		  && I.is_bottom (IntervalAnalysis.output map v))
	      then begin
		Cfg.iter_succ_e (Cfg.remove_edge_e func.cfg) func.cfg v;
		Log.debug ("UNREACHABLE: " ^ (Def.show v));
		v.dkind <- Builtin Exit;
		changed := true
	      end
	  | _ -> ()
      in
      let init = Cfg.initial_vertex func.cfg in
	Cfg.iter_vertex remove_vertex func.cfg;
	CfgIr.remove_unreachable func.cfg init;
    in
      List.iter process_func file.funcs
  in
  let construct_dg  =
    if !must_alias then Dep.construct_dg else TrivDep.construct_dg
  in
  let rec go () =
    let dg = Log.phase "Construct DG" construct_dg file in
    let state = IntervalAnalysis.mk_state dg in
    let map = IntervalAnalysis.do_analysis state dg in
      Log.debug "REMOVE UNREACHABLE";
      changed := false;
      remove_unreachable dg map file;
      if !changed then go () else (dg, map)
  in
    ignore (Bddpa.initialize file);
    Pa.simplify_calls file;
    let (dg,map) = go () in
      IntervalAnalysis.check_assertions dg map

(* Count the number of edges e where at least of the access paths labeling e
   is a memory location (i.e., not a variable) *)
let nb_complex_edges dg =
  let f edge count =
    let is_complex x = match Pack.fst x, Pack.snd x with
      | (Deref _, _) | (_, Deref _) -> true
      | (_, _) -> false
    in
      if Afg.Pack.PairSet.exists is_complex (DG.E.label edge)
      then count + 1
      else count
  in
    DG.fold_edges_e f dg 0

let hdfg_stats file =
  let dg = Log.phase "Construct hDFG" construct_dg file in
    print_endline ("Vertices: " ^ (string_of_int (DG.nb_vertex dg)));
    print_endline ("Edges: " ^ (string_of_int (DG.nb_edges dg)));
    print_endline ("Complex edges: " ^ (string_of_int (nb_complex_edges dg)))


let _ =
  CmdLine.register_pass
    ("-hdfg",
     interval_analysis,
     " Interval analysis with heap data flow graph")
let _ =
  CmdLine.register_pass
    ("-hdfg-stats", hdfg_stats, " Heap data flow graph statistics")
