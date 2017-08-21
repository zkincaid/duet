open Core
open CfgIr
open Apak
open Ark

(* TODO: Address of generates no equality *)
(* -----------------Domains *)
module type Predicate = sig
  include EqLogic.Hashed.Predicate
  val pred_weight : Def.t -> t
end

module CombinePred (V : EqLogic.Var) (P1 : Predicate with type var = V.t)
    (P2 : Predicate with type var = V.t) =
struct
  type t = P1.t * P2.t [@@deriving show,ord]
  type var = V.t

  let equal x y = (P1.equal (fst x) (fst y)) && (P2.equal (snd x) (snd y))
  let unit = (P1.unit, P2.unit)
  let mul x y = (P1.mul (fst x) (fst y), P2.mul (snd x) (snd y))
  let subst sub_var x = (P1.subst sub_var (fst x), P2.subst sub_var (snd x))
  let implies sub x y = (P1.implies sub (fst x) (fst y)) &&
                        (P2.implies sub (snd x) (snd y))
  let hash = Hashtbl.hash
  let pred_weight def = (P1.pred_weight def, P2.pred_weight def)
end

(* Locksets. acq tracks acuires that definitely have not been released, rel
 * tracks release that may not have been re-acquired. Negation is a hack to
 * test satisfiability of eqs1 ^ eqs2 ^ acq1 \cap acq2 \neq 0 through mul *)
module LockPred = struct
  type var = Var.t
  type t = { acq : AP.Set.t;
             rel : AP.Set.t }
      [@@deriving show,ord]

  let equal l1 l2 = compare l1 l2 = 0
  let unit = { acq = AP.Set.empty;
               rel = AP.Set.empty }
  let mul l1 l2 =
    let remove eq l rel =
      AP.Set.filter (fun x -> not (AP.Set.exists (eq x) rel)) l
    in
    { acq =
        AP.Set.union
          (remove PointerAnalysis.may_alias l1.acq l2.rel)
          l2.acq;
      rel = AP.Set.union (remove AP.equal l1.rel l2.acq) l2.rel }
  (* Not sure if this is the right way to handle existentials *)
  let subst sub_var l =
    let add iap set = match AP.psubst_var sub_var iap with
      | Some z -> AP.Set.add z set
      | None   -> set
    in
    let add_2 iap set = match AP.psubst_var sub_var iap with
      | Some z -> AP.Set.add z set
      | None   -> AP.Set.add (AP.unsubscript iap) set
    in
    { acq = AP.Set.fold add l.acq AP.Set.empty;
      rel = AP.Set.fold add_2 l.rel AP.Set.empty }
  let hash l = Hashtbl.hash (AP.Set.hash l.acq,
                             AP.Set.hash l.rel)
  (* x implies y if x acquires a subset of y and releases a superset of y *)
  let implies sub y x =
    let sub_iap iap =
      match AP.psubst_var (fun x -> Some (sub x)) iap with
      | Some z -> z
      | None -> assert false (* impossible *) in
    let y_sub = { acq = AP.Set.map sub_iap y.acq;
                  rel = AP.Set.map sub_iap y.rel }
    in
    (AP.Set.for_all (fun k -> AP.Set.mem k y_sub.acq) x.acq) &&
    (AP.Set.for_all (fun k -> AP.Set.mem k x.rel) y_sub.rel)

  let pred_weight def =
    let get_deref e = match e with
      | AddrOf ap -> AP.Set.singleton ap
      | _         -> AP.Set.singleton (Deref e)
    in match def.dkind with
    | Builtin (Acquire e) -> { acq = get_deref e;
                               rel = AP.Set.empty }
    | Builtin (Release e) -> { acq = AP.Set.empty;
                               rel = get_deref e }
    | _ -> unit
end

module CoLockPred = struct
  open LockPred
  include CombinePred(Var)(LockPred)(LockPred)
  let inter (l1, l2) = AP.Set.inter l1.acq l2.acq
  let inter_empty ls = AP.Set.is_empty (inter ls)
  let left ls  = (ls, LockPred.unit)
  let right ls = (LockPred.unit, ls)
end

module MakePath (P : Predicate with type var = Var.t) = struct
  type var = Var.t
  module Minterm    = EqLogic.Hashed.MakeEQ(Var)(P)
  module Formula    = EqLogic.MakeFormula(Minterm)
  module Transition = Formula.Transition
  include Transition

  let weight def =
    let pw = P.pred_weight def in
    let weight_builtin bi = match bi with
      | Acquire e
      | Release e -> assume Bexpr.ktrue (Aexpr.free_vars e) pw
      | Alloc (v, e, targ) -> assign (Variable v) (Havoc (Var.get_type v)) pw
      | Free _
      | Fork (_, _, _)
      | PrintBounds _
      | AtomicBegin
      | AtomicEnd          -> one
      | Exit               -> zero
    in match def.dkind with
    | Assign (v, e)        -> assign (Variable v) e pw
    | Store  (a, e)        -> assign a e pw
    | Call   (vo, e, elst) -> failwith "Lock logic: Call encountered"
    | Assume be
    | Assert (be, _)       -> assume be (Bexpr.free_vars be) pw
    | AssertMemSafe (e, s) -> assume (Bexpr.of_aexpr e) (Aexpr.free_vars e) pw
    | Initial              -> one
    | Return eo            -> failwith "Lock logic: Return encountered"
    | Builtin bi -> weight_builtin bi
end

module LockPath = MakePath(LockPred)
module CoLockPath = MakePath(CoLockPred)

(* zero all locksets in a transition formula *)
let zero_locks lp =
  let lp_frame = LockPath.get_frame lp in
  let make_minterm mt =
    LockPath.Minterm.make (LockPath.Minterm.get_eqs mt) LockPred.unit
  in
  let add_minterm mt  =
    LockPath.add (LockPath.of_minterm lp_frame (make_minterm mt))
  in
  LockPath.fold_minterms add_minterm lp LockPath.zero

let interleave lp1 lp2 =
  let frame = Var.Set.union (LockPath.get_frame lp1) (LockPath.get_frame lp2) in
  let sub  = LockPath.Minterm.subst (fun x -> if Var.get_subscript x = 1
                                      then Var.subscript x 3
                                      else x)
  in
  let g m1 m2 =
    let ls = (LockPath.Minterm.get_pred m1, LockPath.Minterm.get_pred m2) in
    let eqs = LockPath.Minterm.get_eqs (LockPath.Minterm.mul m1 (sub m2)) in
    let m3 = CoLockPath.Minterm.make eqs ls in
    CoLockPath.add (CoLockPath.of_minterm frame m3)
  in
  let f m1 = LockPath.fold_minterms (fun m2 -> g m1 m2) lp2 in
  LockPath.fold_minterms f lp1 CoLockPath.zero

let lift_left lp =
  let frame = LockPath.get_frame lp in
  let f m =
    let eqs = LockPath.Minterm.get_eqs m in
    let ls = LockPath.Minterm.get_pred m in
    let m' = CoLockPath.Minterm.make eqs (CoLockPred.left ls) in
    CoLockPath.add (CoLockPath.of_minterm frame m')
  in
  LockPath.fold_minterms f lp CoLockPath.zero

let lift_none lp =
  let frame = LockPath.get_frame lp in
  let f m =
    let eqs = LockPath.Minterm.get_eqs m in
    let m' = CoLockPath.Minterm.make eqs CoLockPred.unit in
    CoLockPath.add (CoLockPath.of_minterm frame m')
  in
  LockPath.fold_minterms f lp CoLockPath.zero

module DefUse = struct
  type t = Var.t * Def.t [@@deriving show,ord]
  let equal x y = compare x y = 0
end

module LockMon = Ka.Ordered.AdditiveMonoid(LockPath)
module CoLockMon = Ka.Ordered.AdditiveMonoid(CoLockPath)

module DefMap = Monoid.FunctionSpace.Total.Ordered.Make(Var)(LockMon)
module UseMap = Monoid.FunctionSpace.Total.Ordered.Make(Def)(LockMon)
module DUMap = Monoid.FunctionSpace.Total.Ordered.Make(DefUse)(CoLockMon)

let filter_du du =
  let frame = CoLockPath.get_frame du in
  let f min acc =
    let ls = CoLockPath.Minterm.get_pred min in
    if CoLockPred.inter_empty ls
    then CoLockPath.add (CoLockPath.of_minterm frame min) acc
    else acc
  in
  CoLockPath.fold_minterms f du CoLockPath.zero

let def_mul_l x y =
  DefMap.map (fun tr -> LockPath.mul y tr) x

let def_mul_l_con x y =
  DefMap.map (fun tr -> LockPath.mul (zero_locks y) tr) x

let use_mul_l x y =
  UseMap.map (fun tr -> LockPath.mul y tr) x

let use_mul_l_con x y =
  UseMap.map (fun tr -> LockPath.mul (zero_locks y) tr) x

let du_mul_l x y =
  let y' = lift_left y in
  DUMap.map (fun tr -> filter_du (CoLockPath.mul y' tr)) x

let du_mul_l_con x y =
  let y' = lift_none y in
  DUMap.map (fun tr -> filter_du (CoLockPath.mul y' tr)) x

let mul_du def use =
  let h (v, def_tr) acc (use, use_tr) =
    let tr = filter_du (interleave def_tr use_tr) in
    DUMap.update (v, use) (filter_du tr) acc
  in
  let g acc (v, def_tr) =
    BatEnum.fold (h (v, def_tr)) acc (UseMap.enum use)
  in
  BatEnum.fold g DUMap.unit (DefMap.enum def)

let mul_ud def use =
  let h (v, def_tr) acc (use, use_tr) =
    let tr = filter_du (interleave use_tr def_tr) in
    DUMap.update (v, use) tr acc
  in
  let g acc (v, def_tr) =
    BatEnum.fold (h (v, def_tr)) acc (UseMap.enum use)
  in
  BatEnum.fold g DUMap.unit (DefMap.enum def)

(* Domain for the data race analysis *)
module Domain = struct
  type var = Var.t
  type t = { lp : LockPath.t;
             def   : DefMap.t;
             def_c : DefMap.t;
             use   : UseMap.t;
             use_c : UseMap.t;
             du    : DUMap.t;
             du_c  : DUMap.t }
      [@@deriving show,ord]

  let equal a b = compare a b = 0
  let mul a b =
    let bdef = def_mul_l b.def a.lp in
    let bdef_c = def_mul_l_con b.def_c a.lp in
    let buse = use_mul_l b.use a.lp in
    let buse_c = use_mul_l_con b.use_c a.lp in
    { lp = LockPath.mul a.lp b.lp;
      def   = DefMap.mul a.def bdef;
      def_c = DefMap.mul a.def_c bdef_c;
      use   = UseMap.mul a.use buse;
      use_c = UseMap.mul a.use_c buse_c;
      du    = DUMap.mul
          (DUMap.mul a.du (du_mul_l b.du a.lp))
          (DUMap.mul (mul_du bdef a.use_c) (mul_ud a.def_c buse));
      du_c  = DUMap.mul
          (DUMap.mul a.du_c (du_mul_l_con b.du_c a.lp))
          (DUMap.mul (mul_du a.def_c buse_c) (mul_du bdef_c a.use_c)) }
  let add a b = { lp = LockPath.add a.lp b.lp;
                  def   = DefMap.mul a.def b.def;
                  def_c = DefMap.mul a.def_c b.def_c;
                  use   = UseMap.mul a.use b.use;
                  use_c = UseMap.mul a.use_c b.use_c;
                  du    = DUMap.mul a.du b.du;
                  du_c  = DUMap.mul a.du_c b.du_c }
  let zero = { lp = LockPath.zero;
               def   = DefMap.unit;
               def_c = DefMap.unit;
               use   = UseMap.unit;
               use_c = UseMap.unit;
               du    = DUMap.unit;
               du_c  = DUMap.unit }
  let one = { lp = LockPath.one;
              def   = DefMap.unit;
              def_c = DefMap.unit;
              use   = UseMap.unit;
              use_c = UseMap.unit;
              du    = DUMap.unit;
              du_c  = DUMap.unit }
  let star a =
    let lp = LockPath.star a.lp in
    let def   = def_mul_l a.def lp in
    let def_c = def_mul_l_con a.def_c lp in
    let use   = use_mul_l a.use lp in
    let use_c = use_mul_l_con a.use_c lp in
    { lp    = lp;
      def   = def;
      def_c = def_c;
      use   = use;
      use_c = use_c;
      du    = DUMap.mul (mul_du def use_c) (mul_ud def_c use);
      du_c  = mul_du def_c use_c }
  let exists f a =
    let def_remove_locals m =
      let g acc (v, tr) =
        if f v then DefMap.update v (LockPath.exists f tr) acc else acc
      in
      BatEnum.fold g DefMap.unit (DefMap.enum m)
    in
    let use_remove_locals m =
      let g acc (def, tr) =
        UseMap.update def (LockPath.exists f tr) acc
      in
      BatEnum.fold g UseMap.unit (UseMap.enum m)
    in
    let du_remove_locals m =
      let g acc (x, tr) =
        DUMap.update x (CoLockPath.exists f tr) acc
      in
      BatEnum.fold g DUMap.unit (DUMap.enum m)
    in
    { lp = LockPath.exists f a.lp;
      def   = def_remove_locals a.def;
      def_c = def_remove_locals a.def_c;
      use   = use_remove_locals a.use;
      use_c = use_remove_locals a.use_c;
      du    = du_remove_locals  a.du;
      du_c  = du_remove_locals  a.du_c }
  let widen = add
  let fork a =
    { lp = LockPath.one;
      def   = DefMap.unit;
      def_c = DefMap.mul a.def a.def_c;
      use   = UseMap.unit;
      use_c = UseMap.mul a.use a.use_c;
      du    = DUMap.unit;
      du_c  = DUMap.mul a.du a.du_c }
end

let get_func e = match Aexpr.strip_all_casts e with
  | AccessPath (Variable (func, voff)) -> func
  | AddrOf     (Variable (func, voff)) -> func
  | _  -> failwith "Lock Logic: Called/Forked expression not a function"

module Datarace = struct
  module LSA = Interproc.MakeParPathExpr(Domain)
  open Domain

  (* The weight function needs a hash table of summaries, and a weight function for lockpath *)
  let weight wt d =
    let lp = wt d in
    let uses = UseMap.update d lp UseMap.unit in
    match d.dkind with
    | Assign (v, e) when Var.is_shared v ->
      { lp = lp;
        def   = DefMap.update v lp DefMap.unit;
        def_c = DefMap.unit;
        use   = uses;
        use_c = UseMap.unit;
        du    = DUMap.unit;
        du_c  = DUMap.unit; }
    | _ -> { lp = lp;
             def   = DefMap.unit;
             def_c = DefMap.unit;
             use   = uses;
             use_c = UseMap.unit;
             du    = DUMap.unit;
             du_c  = DUMap.unit }

  let find_all_races query root =
    let ht = Def.HT.create 32 in
    let summary = LSA.get_summary query root in
    let g min acc =
      let ls = CoLockPath.Minterm.get_pred min in
      acc || CoLockPred.inter_empty ls
    in
    let f ((v, def), tr) =
      if CoLockPath.fold_minterms g tr false
      then try Def.HT.replace ht def (Var.Set.add v (Def.HT.find ht def))
        with Not_found -> Def.HT.add ht def (Var.Set.singleton v)
    in
    BatEnum.iter f (DUMap.enum summary.du);
    BatEnum.iter f (DUMap.enum summary.du_c);
    ht

  (* Given wt, a transition formula over lock logic and some predicates,
   * construct a stabilized transition formula *)
  let stabilise races wt def =
    let pre =
      let frame = try Def.HT.find races def with Not_found -> Var.Set.empty in
      LockPath.of_minterm frame (LockPath.Minterm.unit)
    in
    let post =
      let frame = try Def.HT.find races def with Not_found -> Var.Set.empty in
      LockPath.of_minterm frame (LockPath.Minterm.unit)
    in
    LockPath.mul pre (LockPath.mul (wt def) post)

  let eq_races r1 r2 =
    let f k v s = s && List.exists (Var.Set.equal v) (Def.HT.find_all r1 k) in
    Def.HT.fold f r2 true

  let solve rg root =
    let compute_races races =
      let l_weight = stabilise races LockPath.weight in
      let query = LSA.mk_query rg (weight l_weight) Interproc.local root
      in
      LSA.remove_dead_code query;
      find_all_races query root
    in
    let rec fp_races old_races =
      let new_races = compute_races old_races in
      if eq_races old_races new_races then new_races
      else fp_races new_races
    in
    let init_races = Def.HT.create 0 in
    Log.phase "(Pseudo) Datarace analysis" fp_races init_races


  let init file =
    match file.entry_points with
    | [main] -> begin
        let rg = Interproc.make_recgraph file in
        solve rg main
      end
    | _      -> assert false
end

let races = ref None
let get_races () = match !races with
  | Some x -> x
  | None ->
    let dra = Datarace.init (CfgIr.get_gfile()) in
    races := Some dra;
    dra
let find_races rg root = match !races with
  | Some x -> x
  | None ->
    let dra = Datarace.solve rg root in
    races := Some dra;
    dra
let compute_races rg root = 
  let dra = Datarace.solve rg root in
  races := Some dra;
  dra

module Stabilizer (Min : EqLogic.Hashed.ConjFormula with type var = Var.t) = struct
  module Formula = EqLogic.MakeFormula(Min)
  module Trans   = Formula.Transition
  let stabilise wt def =
    let races = get_races () in
    let pre =
      let frame = try Def.HT.find races def with Not_found -> Var.Set.empty in
      Trans.of_minterm frame (Min.unit)
    in
    let post =
      let frame = try Def.HT.find races def with Not_found -> Var.Set.empty in
      Trans.of_minterm frame (Min.unit)
    in
    Trans.mul pre (Trans.mul (wt def) post)
end

let analyze file =
  let dra = get_races () in
  let f def v =
    Format.printf "%a --> %a" Def.pp def Var.Set.pp v
  in
  Def.HT.iter f dra

let _ =
  CmdLine.register_pass
    ("-dra", analyze, " Data race analysis")
