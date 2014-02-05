(*pp camlp4find deriving.syntax *)

(** Common operations for pointer analyses *)

open Core
open Apak
open CfgIr

type membase =
  | MAddr of varinfo
  | MStr of string
  | MAlloc of def
  | MTmp of int (** Temporary memory location - does not correspond to anything
		    in the program *)
      deriving (Compare)

(** A memory location consists of a base and an offset.  The location of
    (base,offset) is base+offset if offset is fixed, and some nondeterministic
    location *within the chunk of memory allocated at base* if offset is
    OffsetUnknown. *)
type memloc = membase * offset
    deriving (Compare)

module MemBase = struct
  module Elt = struct
    type t = membase deriving (Compare)
    include Putil.MakeFmt(struct
      type a = t
      let format formatter = function
      | MAddr x -> Format.fprintf formatter "&%a" Varinfo.format x
      | MAlloc x -> Format.fprintf formatter "alloc#%d" x.did
      | MStr x -> Format.pp_print_string formatter ("string#" ^ x)
      | MTmp x -> Format.fprintf formatter "tmp#%d" x
    end)
    let compare = Compare_t.compare
    let equal x y = compare x y = 0
    let hash = function
      | MAddr x -> Hashtbl.hash (0, Varinfo.hash x)
      | MAlloc x -> Hashtbl.hash (1, Def.hash x)
      | MStr x -> Hashtbl.hash (2, x)
      | MTmp x -> Hashtbl.hash (3, x)
  end
  include Putil.MakeCoreType(Elt)
  let is_shared = function
    | MAddr vi -> begin match Varinfo.get_visibility vi with
      | VzGlobal -> true
      | VzThreadLocal | VzLocal -> false
    end
    | MStr _ -> false
    | MAlloc _ -> true
    | MTmp _ -> false

end

module MemLoc = struct
  module Elt = struct
    type t = memloc deriving (Compare)
    include Putil.MakeFmt(struct
      type a = t
      let format formatter (base, offset) = match offset with
	| OffsetFixed 0 -> MemBase.format formatter base
	| _ ->
	  Format.fprintf formatter "%a.%a"
	    MemBase.format base
	    Offset.format offset
    end)
    let hash (base, offset) = Hashtbl.hash (MemBase.hash base, offset)
    let compare = Compare_t.compare
    let equal x y = compare x y = 0
  end
  include Putil.MakeCoreType(Elt)
  let is_shared (x, _) = MemBase.is_shared x
  let is_var = function
    | (MAddr _, _) -> true
    | (_, _)       -> false
end

type 'a value =
  | VConst of int
  | VRhs of 'a

module MakeEval(Rhs : sig
		  type t
		  val str_const : string -> t
		  val addr_of : Var.t -> t
		  val havoc : t
		  val change_offset : (int -> offset) -> t -> t
		  val join : t -> t -> t
		end) =
struct
  let forget_offset = Rhs.change_offset (fun _ -> OffsetUnknown)
  let rec eval expr env =
    let f = function
      | OHavoc _ -> VRhs Rhs.havoc
      | OConstant (CInt (x, _)) -> VConst x
      | OConstant (CString str) -> VRhs (Rhs.str_const str)
      | OConstant _ -> VRhs Rhs.havoc
      | OCast (_, x) -> x
      | OBinaryOp (VConst a, op, VConst b, _) -> VConst (eval_binop op a b)
      | OBinaryOp (VRhs a, Add, VConst b, _)
      | OBinaryOp (VConst b, Add, VRhs a, _) ->
	  VRhs (Rhs.change_offset (fun x -> OffsetFixed (x + b)) a)
      | OBinaryOp (VRhs a, Minus, VConst b, _) ->
	  VRhs (Rhs.change_offset (fun x -> OffsetFixed (x - b)) a)
      | OBinaryOp (VConst a, Minus, VRhs b, _) ->
	  VRhs (Rhs.change_offset (fun x -> OffsetFixed (a - x)) b)
      | OBinaryOp (VConst _, _, VRhs a, _)
      | OBinaryOp (VRhs a, _, VConst _, _) -> VRhs (forget_offset a)
      | OBinaryOp (VRhs a, _, VRhs b, _) -> VRhs (forget_offset (Rhs.join a b))
      | OAccessPath ap -> VRhs (env ap)
      | OBoolExpr _ -> VRhs Rhs.havoc
      | OUnaryOp (Neg, VConst x, _) -> VConst (-x)
      | OUnaryOp (BNot, VConst x, _) -> VConst (lnot x)
      | OUnaryOp (_, VRhs a, _) -> VRhs (forget_offset a)
      | OAddrOf ap ->
	  let rec go offset = function
	    | Deref expr -> begin match eval expr env with
		| VConst x -> VConst (x + offset)
		| VRhs rhs ->
		    let f x = OffsetFixed (x + offset) in
		      VRhs (Rhs.change_offset f rhs)
	      end
	    | Variable (var, ofv) ->
		let offset = Offset.add ofv (OffsetFixed offset) in
		  VRhs (Rhs.addr_of (var, offset))
	  in
	    go 0 ap
    in
      Expr.fold f expr
end

(* Simplified access path - these can appear on either side of a pointer
   analysis constraint (but the LHS is always a simple_ap).  A level-0 access
   path accesses the heap 0 times, and a level-1 access path accesses the heap
   once.  Lvl0(v,of) represents the access path v.of, and Lvl1(v,of1,of2)
   represents the access path [*(v.of1)].of2 *)
type simple_ap =
  | Lvl0 of Var.t
  | Lvl1 of Var.t * offset
      deriving (Compare)

module SimpleAP = struct
  module Elt = struct
    type t = simple_ap deriving (Compare)
    include Putil.MakeFmt(struct
      type a = t
      let format formatter = function
	| Lvl0 v -> Var.format formatter v
	| Lvl1 (v, offset) ->
	  Format.fprintf formatter "*(%a)->%a"
	    Var.format v
	    Offset.format offset
    end)
    let compare = Compare_t.compare
  end
  include Elt
  module Set = Putil.Set.Make(Elt)
  let deref = function
    | Lvl0 xv -> Lvl1 (xv, OffsetFixed 0)
    | Lvl1 (_, _) -> failwith "Cannot dereference Lvl1 AP"
end

(* Representation of a right hand side of a pointer analysis constraint *)
type rhsbase =
  | RAp of simple_ap
  | RAddr of varinfo
  | RStr of string
      deriving (Compare)
type simple_rhs = rhsbase * offset deriving (Compare)

module SimpleRhs = struct
  module Elt = struct
    type t = simple_rhs deriving (Compare)
    include Putil.MakeFmt(struct
      type a = t
      let format formatter (base, offset) =
	begin match base with
	| RAp ap -> SimpleAP.format formatter ap
	| RAddr var -> Format.fprintf formatter "&(%a)" Varinfo.format var
	| RStr string ->
	  Format.pp_print_string formatter
	    ("\"" ^ (String.escaped string) ^ "\"")
	end;
	begin match offset with
	| OffsetFixed 0 -> ()
	| _ ->
	  Format.pp_print_string formatter "+";
	  Offset.format formatter offset
	end
    end)
    let compare = Compare_t.compare
  end
  include Elt
  module Set = Putil.Set.Make(Elt)
end

(* Represents an *entire* right hand side of an assignment.  If VConst, then
   the RHS evaluates to a constant integer (and thus cannot evaluate to a
   pointer value); otherwise, it's a set of simple_rhs, each of which
   generates an inclusion constraint with the lhs. *)
(*type simple_val =
  | VConst of int
  | VRhsSet of SimpleRhs.Set.t*)


(******************************************************************************)
(* Compute overapproximations of the values that can be taken by an
   expression/access path as a set of RHSs (with a special case that we
   evaluate constant integer expressions exactly) / set of SAPs *)

module E = MakeEval(
  struct
    type t = SimpleRhs.Set.t
    let change_offset f =
      let change = function
	| (rhs, OffsetFixed off) -> (rhs, f off)
	| x -> x
      in
	SimpleRhs.Set.map change
    let join = SimpleRhs.Set.union
    let havoc = SimpleRhs.Set.empty
    let addr_of v = SimpleRhs.Set.singleton (RAddr (fst v), snd v)
    let str_const str = SimpleRhs.Set.singleton (RStr str, OffsetFixed 0)
  end)

let rec simplify_ap = function
  | Deref expr -> begin match simplify_expr expr with
      | VConst _ -> SimpleAP.Set.empty
      | VRhs set ->
	  let add (rhs, offset) set = match rhs with
	    | RAp (Lvl0 var) ->
		SimpleAP.Set.add (Lvl1 (var, offset)) set
	    | RAp (Lvl1 (_, _)) ->
		let rhs_str = SimpleRhs.show (rhs, offset) in
		Log.log Log.top ("Can't deref Lvl1 AP " ^ rhs_str);
		assert false
	    | RAddr var ->
		(* *(&var + offset) = var[offset] *)
		SimpleAP.Set.add (Lvl0 (var, offset)) set
	    | RStr _ -> set (* (I /think/) it's safe to discard string RHSs,
			       since constant strings are immutable (so once
			       it is derefed it can't point to anything) *)
	  in
	    SimpleRhs.Set.fold add set SimpleAP.Set.empty
    end
  | Variable v -> SimpleAP.Set.singleton (Lvl0 v)
and simplify_expr expr =
  let env ap =
    let add ap set = SimpleRhs.Set.add (RAp ap, OffsetFixed 0) set in
      SimpleAP.Set.fold add (simplify_ap ap) SimpleRhs.Set.empty
  in
    E.eval expr env

class virtual ptr_anal file =
object (self)
  method virtual ap_points_to : ap -> MemLoc.Set.t
  method virtual expr_points_to : expr -> MemLoc.Set.t
  method resolve_call expr =
    let targets = match Expr.strip_casts expr with
      | AccessPath (Deref x) -> self#expr_points_to x
      | AddrOf x -> self#expr_points_to expr
      | expr -> begin
	Log.logf Log.top "Could not resolve call `%a'"
	  Expr.format expr;
	assert false
      end
    in
    let add_call x set = match x with
      | (MAddr v, _) -> Varinfo.Set.add v set
      | _ -> set (* No functions on the heap *)
    in
      MemLoc.Set.fold add_call targets Varinfo.Set.empty

  method has_undefined_target expr =
    let file = get_gfile () in
    let is_undefined target = not (defined_function target file) in
      Varinfo.Set.exists is_undefined (self#resolve_call expr)

  method resolve_ap ap =
    let add sap set = match sap with
      | Lvl0 (var, of1) -> MemLoc.Set.add (MAddr var, of1) set
      | Lvl1 ((var, of1), of2) ->
	  let add_offset (base, offset) = (base, Offset.add offset of2) in
	    MemLoc.Set.map add_offset (self#ap_points_to (Variable (var, of1)))
    in
      SimpleAP.Set.fold add (simplify_ap ap) MemLoc.Set.empty

  method may_alias x y =
    let may_alias x y =
      let memloc_is_alias x y =
	if (snd x) = OffsetUnknown || (snd y) = OffsetUnknown
	then MemBase.equal (fst x) (fst y)
	else MemLoc.equal x y
      in
      let y_aliases = self#resolve_ap y in
	MemLoc.Set.exists
	  (fun x -> MemLoc.Set.exists (memloc_is_alias x) y_aliases)
	  (self#resolve_ap x)
    in

    (* This is a hack to make sure that uninitialized pointers always alias
       themselves (among other things).  It should be safe to remove *provided
       that models are provided for all procedures which allocate memory*. *)
    let is_uninit = function
      | Deref x -> MemLoc.Set.is_empty (self#expr_points_to x)
      | _ -> false
    in
    let is_ptr = function
      | Deref _ -> true
      | _ -> false
    in
      is_uninit x && is_ptr y || is_uninit y && is_ptr x || may_alias x y
end

let instance = ref None
let initialize = ref None

let get_instance () =
  match !instance with
    | Some x -> x
    | None -> begin match !initialize with
      | Some f ->
	let inst = f (CfgIr.get_gfile()) in
	instance := Some inst;
	inst
      | None -> failwith "No instance set for pointer analysis"
    end
let set_pa pa = instance := Some pa
let set_init f = initialize := Some f

let ap_points_to ap = (get_instance ())#ap_points_to ap
let expr_points_to expr = (get_instance ())#expr_points_to expr
let may_alias x y = (get_instance ())#may_alias x y
let resolve_ap ap = (get_instance ())#resolve_ap ap
let resolve_call x = (get_instance ())#resolve_call x
let has_undefined_target expr = (get_instance ())#has_undefined_target expr

let simplify_calls file =
  let pa = get_instance () in
  let get_param =
    Memo.memo
      (fun i -> mk_thread_local_var
	file
	("param" ^ (string_of_int i))
	(Concrete Dynamic))
  in
  let return_var = mk_thread_local_var file "return" (Concrete Dynamic) in
  let simplify_func func =
    let cfg = func.cfg in
    let defs = Cfg.fold_vertex (fun v vs -> v::vs) cfg [] in
    let rec assign_args def i = function
      | [] -> ()
      | (x::xs) ->
	let loc = Def.get_location def in
	let assign = Def.mk ~loc:loc (Assign (get_param i, x)) in
	insert_pre assign def cfg;
	assign_args def (i+1) xs
    in
    let rec assign_params init_vertex i = function
      | [] -> ()
      | (x::xs) ->
	let assign =
	  Def.mk (Assign (Var.mk x,
			  AccessPath (Variable (get_param i))))
	in
	insert_pre assign init_vertex cfg;
	assign_params init_vertex (i+1) xs
    in
    (* Replace an indirect function call with a nondeterministic branch
       between all its possible (direct) targets.  TODO: This transformation
       is an overapproximation, but it can be made exact. *)
    let resolve_call def func cfg =
      let targets = pa#resolve_call func in
      let loc = Def.get_location def in
      let skip = Def.mk (Assume (Bexpr.ktrue)) in
      let add_call target =
	let call =
	  Def.mk ~loc:loc (Call (None,
				 Expr.addr_of (Variable (Var.mk target)),
				 []))
	in
	Cfg.add_vertex cfg call;
	Cfg.add_edge cfg def call;
	Cfg.add_edge cfg call skip;
      in
      def.dkind <- Assume (Bexpr.ktrue);
      insert_succ skip def cfg;
      Cfg.remove_edge cfg def skip;
      assert (Varinfo.Set.cardinal targets >= 1); (* todo *)
      Varinfo.Set.iter add_call targets
    in
    let simplify_def def = match def.dkind with
      | Call (Some lhs, func, args) ->
	let loc = Def.get_location def in
	let assign =
	  let rhs =
	    if pa#has_undefined_target func then Havoc (Var.get_type lhs)
	    else AccessPath (Variable return_var)
	  in
	  Def.mk ~loc:loc (Assign (lhs, rhs))
	in
	assign_args def 0 args;
	resolve_call def func cfg;
	insert_succ assign def cfg
      | Call (None, func, args) ->
	assign_args def 0 args;
	resolve_call def func cfg
      | Return (Some x) ->
	def.dkind <- Assign (return_var, x)
      | Return None ->
	def.dkind <- Assign (return_var, Havoc (Concrete Dynamic))
      | _ -> ()
    in
    List.iter simplify_def defs;
    assign_params (Cfg.initial_vertex cfg) 0 func.formals
  in
  List.iter simplify_func file.funcs

let ap_is_shared ap = MemLoc.Set.exists MemLoc.is_shared (resolve_ap ap)
