(*pp camlp4find deriving.syntax *)

open Core
open CfgIr
open Apak

(* -----------------Concurrent analysis *)
module Conc = struct
  module V = struct
    include Def
    type atom = t
    type block = Varinfo.t
    let classify v = match v.dkind with
      | Call (None, AddrOf (Variable (func, OffsetFixed 0)), []) ->
          RecGraph.Block func
      | Call (_, _, _) ->
          Log.errorf "Unrecognized call: %a" format v;
          assert false
      | Builtin (Fork (vo, e, elst)) -> 
          begin match Expr.strip_all_casts e with
            | AccessPath (Variable (func, OffsetFixed 0)) -> RecGraph.Block func
            | _ -> Log.errorf "Unrecognized fork: %a" format v;
                   assert false
          end
      | _ -> RecGraph.Atom v
  end
  module RG = RecGraph.Make(V)(Varinfo)
  module RGD = ExtGraph.Display.MakeSimple(RG.G)(Def)
  module MakePathExpr = Pathexp.MakeRG(RG)(Varinfo)
  
  let make_recgraph file =
    ignore (Bddpa.initialize file);
    Pa.simplify_calls file;
    let mk_func rg func =
      let add_edge src tgt graph = RG.G.add_edge graph src tgt in
      let graph = Cfg.fold_edges add_edge func.cfg RG.G.empty in
      let bentry = Cfg.initial_vertex func.cfg in
      let ts = Cfg.enum_terminal func.cfg in
      let bexit = Def.mk (Assume Bexpr.ktrue) in
      let add_edge graph v = RG.G.add_edge graph v bexit in
      let graph = BatEnum.fold add_edge (RG.G.add_vertex graph bexit) ts in
        RG.add_block rg func.fname graph ~entry:bentry ~exit:bexit
    in
      List.fold_left mk_func RG.empty file.funcs
end

(* -----------------Domains *)
module type Predicate = sig
  include EqLogic.Hashed.Predicate
  val pred_weight : Def.t -> t
end

  (* Don't like this solution at all *)
module NullPred = struct
  type t = char deriving (Show,Compare)
  type var = Var.t
  let compare = Compare_t.compare
  let format = Show_t.format
  let show = Show_t.show
  let equal _ _ = true
  let unit = '0'
  let mul _ _ = '0'
  let subst _ _ = '0'
  let hash = Hashtbl.hash
  let implies _ _ _ = true
  let pred_weight _ = unit
end

module LockPred = struct
  type t = { acq : AP.Set.t;
             rel : AP.Set.t } 
             deriving (Show,Compare)
  type var = Var.t
  let compare = Compare_t.compare
  let format = Show_t.format
  let show = Show_t.show

  (* Effectively tests whether the actual locksets are equivalent, regardless of
   * the releases *)
  let equal l1 l2 = AP.Set.equal l1.acq l2.acq
  let unit = { acq = AP.Set.empty;
               rel = AP.Set.empty }
  let mul l1 l2 =
    let deref_alias x y = Pa.may_alias (Deref (AccessPath x)) (Deref (AccessPath y)) in
    let remove l rel = 
      AP.Set.filter (fun x -> not (AP.Set.exists (Pa.may_alias x) rel)) l
    in 
      { acq = AP.Set.union (remove l1.acq l2.rel) l2.acq;
        rel = AP.Set.union l1.rel l2.rel }
  (* Not sure if this is the right way to handle existentials *)
  let subst sub_var l =
    let add iap set = match AP.psubst_var sub_var iap with
      | Some z -> AP.Set.add z set
      | None   -> set
    in
      { acq = AP.Set.fold add l.acq AP.Set.empty;
        rel = AP.Set.fold add l.rel AP.Set.empty }
  let hash l = Hashtbl.hash (AP.Set.hash l.acq, AP.Set.hash l.rel)
  let implies sub x y =
    let sub_iap iap =
      match AP.psubst_var (fun x -> Some (sub x)) iap with
        | Some z -> z
        | None -> assert false (* impossible *) in
    let y_sub = { acq = AP.Set.map sub_iap y.acq;
                  rel = AP.Set.map sub_iap y.rel }
    in
      (AP.Set.for_all (fun k -> AP.Set.mem k x.acq) y_sub.acq) &&
      (AP.Set.for_all (fun k -> AP.Set.mem k x.rel) y_sub.rel)

  let pred_weight def = match def.dkind with
    | Builtin (Acquire (AccessPath ap)) -> { acq = AP.Set.singleton (Deref (AccessPath ap));
                                             rel = AP.Set.empty }
    | Builtin (Acquire (AddrOf ap)) -> { acq = AP.Set.singleton ap;
                                         rel = AP.Set.empty }
    | Builtin (Release (AccessPath ap)) -> { acq = AP.Set.empty;
                                             rel = AP.Set.singleton (Deref (AccessPath ap)) }
    | Builtin (Release (AddrOf ap)) -> { acq = AP.Set.empty;
                                         rel = AP.Set.singleton ap }
    | _ -> unit
end

module MakePath (P : Predicate with type var = Var.t) = struct
  type var = Var.t
  module Minterm    = EqLogic.Hashed.MakeEQ(Var)(P)
  module Formula    = EqLogic.MakeFormula(Minterm)
  module Transition = Formula.Transition
  include Transition

  let weight def = 
    let hack = Atom (Eq, Constant (CChar 'h'), Constant (CChar 'h')) in
    let pw = P.pred_weight def in
    let weight_builtin bi = match bi with
      | Acquire e -> begin match e with
          | AccessPath ap  -> assume hack (AP.free_vars ap) pw
          | AddrOf ap      -> assume hack (AP.free_vars ap) pw
          | _              -> failwith "Lock logic: I don't think you acquired an access path yo"
        end
      | Release e -> begin match e with
          | AccessPath ap  -> assume hack (AP.free_vars ap) pw
          | AddrOf ap      -> assume hack (AP.free_vars ap) pw
          | _              -> failwith "Lock logic: I don't think you released an access path yo"
        end
      | Alloc (v, e, targ) -> assign (Variable v) (Havoc (Var.get_type v)) pw
      | Free e             -> one
      | Fork (vo, e, elst) -> one
      | AtomicBegin        -> one
      | AtomicEnd          -> one
      | Exit               -> zero
    in match def.dkind with
      | Assign (v, e)        -> assign (Variable v) e pw
      | Store  (a, e)        -> assign a e pw
      | Call   (vo, e, elst) -> failwith "Lock logic: Not sure there are supposed to be calls?"
      | Assume be            -> assume be (Bexpr.free_vars be) pw
      | Assert (be, s)       -> assume be (Bexpr.free_vars be) pw
      | AssertMemSafe (e, s) -> assume (Bexpr.of_expr e) (Expr.free_vars e) pw
      | Initial              -> one 
      | Return eo            -> failwith "Lock logic: Again, not sure about returns..."
      | Builtin bi -> weight_builtin bi
end

module NullPath = MakePath(NullPred)
module LockPath = MakePath(LockPred)

module Mapped (Key : Putil.CoreType) (Value : Putil.Ordered) = struct
  module M = Key.Map
  type t = Value.t M.t
  module Show_t = struct
    type a = t
    let format f a = M.format Value.format f a
    let format_list f a = ()
    let show a =
      let f k v s = s ^ "[" ^ Key.show k ^ "-->" ^ Value.show v ^ "]," in
        M.fold f a ""
    let show_list = List.fold_left (fun acc -> fun a -> acc ^ ", [" ^ show a ^ "],") ""
  end
  module Compare_t = struct
    type a = t
    let compare a b = M.compare Value.compare a b
  end
  let format = Show_t.format
  let show = Show_t.show
  let compare = Compare_t.compare
  let bot = M.empty
  let merge jn a b = 
    let f k av bv = match (av, bv) with
      | (Some phi, Some psi) -> Some (jn phi psi)
      | (Some phi, _)        -> Some phi
      | (_,        Some psi) -> Some psi
      | (_, _)               -> None in
    M.merge f a b
end

(* Protected Definitions *)
module PD = struct
  include Mapped(Var)(LockPath)
  type var = Var.t

  let equal = M.equal LockPath.equal
  let join = merge LockPath.add
  let mul_r a np =
    let np_frame = NullPath.get_frame np in
    let make_minterm m = LockPath.Minterm.make (NullPath.Minterm.get_eqs m) LockPred.unit in
    let add_minterm m acc = LockPath.add (LockPath.of_minterm np_frame (make_minterm m)) acc in
    let lift_np = NullPath.fold_minterms add_minterm np LockPath.zero in
      M.map (fun lp -> LockPath.mul lp lift_np) a
  let mul_l lp a = M.map (fun lp2 -> LockPath.mul lp lp2) a
  let exists f a = M.map (fun lp -> LockPath.exists f lp) a
end

(* Fork maps *)
module FM = struct
  include Mapped(Def)(PD)
  type var = Var.t

  let equal = M.equal PD.equal
  let join = merge PD.join
  let mul_r a np = M.map (fun f -> PD.mul_r f np) a
  let mul_l lp a = M.map (fun f -> PD.mul_l lp f) a
  let exists f a = M.map (fun g -> PD.exists f g) a
  let absorb a pd = M.map (PD.join pd) a
end

module Domain = struct
  type var = Var.t
  type t = { lp : LockPath.t;
             np : NullPath.t;
             seq : PD.t;
             con : PD.t;
             frk : FM.t }
             deriving(Show,Compare)
  let compare = Compare_t.compare
  let format = Show_t.format
  let show = Show_t.show

  let equal a b = (LockPath.equal a.lp b.lp) && 
                  (NullPath.equal a.np b.np) &&
                  (PD.equal a.seq b.seq) &&
                  (PD.equal a.con b.con) &&
                  (FM.equal a.frk b.frk)
  let mul a b =
    let aseq = PD.mul_r a.seq b.np in
    let bseq = PD.mul_l a.lp b.seq in
      { lp = LockPath.mul a.lp b.lp;
        np = NullPath.mul a.np b.np;
        seq = PD.join aseq bseq;
        con = PD.join a.con b.con;
        frk = FM.join (FM.absorb (FM.mul_r a.frk b.np) bseq) (FM.mul_l a.lp b.frk) }
  let add a b = { lp = LockPath.add a.lp b.lp;
                  np = NullPath.add a.np b.np;
                  seq = PD.join a.seq b.seq;
                  con = PD.join a.con b.con;
                  frk = FM.join a.frk b.frk }
  let zero = { lp = LockPath.zero;
               np = NullPath.zero;
               seq = PD.bot;
               con = PD.bot;
               frk = FM.bot } 
  let one = { lp = LockPath.one;
              np = NullPath.one;
              seq = PD.bot;
              con = PD.bot;
              frk = FM.bot }
  let star a = 
    let l = LockPath.star a.lp in
    let n = NullPath.star a.np in
      { lp = l; 
        np = n; 
        seq = PD.mul_l l (PD.mul_r a.seq n);
        con = a.con;
        frk = FM.mul_l l (FM.mul_r a.frk n) }
  let exists f a = { lp = LockPath.exists f a.lp;
                     np = NullPath.exists f a.np;
                     seq = PD.exists f a.seq;
                     con = PD.exists f a.con;
                     frk = FM.exists f a.frk }
  let widen = add
end

module Test = Conc.MakePathExpr(Domain)

let get_func e = match Expr.strip_all_casts e with
  | AccessPath (Variable (func, voff)) -> func
  | AddrOf     (Variable (func, voff)) -> func
  | _  -> failwith "Lock Logic: Called/Forked expression not a function"

let weight imap sums def = 
  let open Domain in 
  let fpoints = try Def.HT.find_all imap def
                with Not_found -> []
  in
  let lsum = 
    let f a (b, v) =
      let summary = try Test.HT.find sums b
                    with Not_found -> Domain.zero 
      in
      let lval = try FM.M.find v summary.frk with Not_found -> PD.bot
      in
        PD.join a lval
    in
      List.fold_left f PD.bot fpoints
  in
    match def.dkind with
      | Call (vo, e, elst) ->
          begin 
            try Test.HT.find sums (get_func e)
            with Not_found -> zero
          end
      | Builtin (Fork (vo, e, elst)) -> 
          let summary = try Test.HT.find sums (get_func e)
          with Not_found -> zero 
          in
            { lp = LockPath.one; 
              np = NullPath.one; 
              seq = PD.bot;
              con = PD.join summary.seq summary.con;
              frk = FM.M.add def PD.bot FM.M.empty }
      | Assign (v, e) -> 
          let l = LockPath.weight def in
            { lp = l;
              np = NullPath.weight def;
              seq = PD.M.add v l PD.M.empty;
              con = PD.bot;
              frk = FM.bot }
      | _ -> { lp = LockPath.weight def;
               np = NullPath.weight def;
               seq = PD.bot;
               con = lsum;
               frk = FM.bot }

let may_race v d =
  try 
    let defs = PD.M.find v d.Domain.con in
    let fold_con seq_path con_path acc =
      let l = LockPath.Minterm.get_pred seq_path in
      let l' = LockPath.Minterm.get_pred con_path in
        acc || AP.Set.is_empty (AP.Set.inter l.LockPred.acq l'.LockPred.acq)
    in
    let fold_seq seq_path acc = acc ||
      LockPath.fold_minterms (fold_con seq_path) defs false
    in
      LockPath.fold_minterms fold_seq d.Domain.lp false
  with Not_found -> false

let analyze file =
  match file.entry_points with
  | [main] -> begin
    let rg = Conc.make_recgraph file in
    let fmap = 
      let ht = Def.HT.create 32 in
      let f (b, v) = match v.dkind with
        | Builtin (Fork (vo, e, elst)) -> Def.HT.add ht (Conc.RG.block_entry rg (get_func e)) (b, v)
        | _ -> ()
      in 
        begin
          BatEnum.iter f (Conc.RG.vertices rg);
          ht
        end
    in
    let local func_name =
      let func = lookup_function func_name (get_gfile()) in
      let vars = Varinfo.Set.remove (return_var func_name)
                   (Varinfo.Set.of_enum (BatEnum.append (BatList.enum func.formals)
                                                        (BatList.enum func.locals)))
      in fun (x, _) -> (Varinfo.Set.mem x vars) in
    let sum_eq sum1 sum2 = 
      let f k v s = s && List.exists (Domain.equal v) (Test.HT.find_all sum1 k) in
        Test.HT.fold f sum2 true in
    let rec iter_query old_query = 
      let new_query = Test.mk_query rg (weight fmap (Test.get_summaries old_query)) local main in
        begin
          Test.compute_summaries new_query;
          if sum_eq (Test.get_summaries old_query) (Test.get_summaries new_query)
            then new_query
            else iter_query new_query 
        end in
    let query =
      let q = (Test.mk_query rg (weight fmap (Test.HT.create 0)) local main) in
        begin
          Test.compute_summaries q;
          iter_query q
        end in
    let iter_vars def =
      let f v = print_endline ((Var.show v) ^ " :: " 
                            ^ (string_of_bool (may_race v (Test.single_src query main def))))
      in
        Var.Set.iter f (Def.free_vars def)
    in
      BatEnum.iter (fun (b, v) -> begin print_endline (String.concat "" [(Def.show v);":"]);
                                        iter_vars v;
                                        print_endline (Domain.show (Test.single_src query main v))
                                  end)
                   (Conc.RG.vertices rg);
      flush stdout
    end
  | _      -> assert false

let _ =
  CmdLine.register_pass
    ("-dra", analyze, " Data race analysis")
