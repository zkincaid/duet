(*pp camlp4find deriving.syntax *)

open Core
open CfgIr
open Apak

(* TODO: Address of generates no equality *)
(* TODO: Fix propagation of forked threads from parent to child
 * e.g. parents forks foo and bar, bar computes concurrently with foo *)
(* -----------------Domains *)
module type Predicate = sig
  include EqLogic.Hashed.Predicate
  val pred_weight : Def.t -> t
end

(* Lock Logic. acq tracks acuires that definitely have not been released, rel
 * tracks release that may not have been re-acquired. Negation is a hack to
 * test satisfiability of eqs1 ^ eqs2 ^ acq1 \cap acq2 \neq 0 through mul *)
module LockPred = struct
  type parity = Pos | Neg deriving(Show,Compare)
  type var = Var.t
  type t = { par : parity;
             acq : AP.Set.t;
             rel : AP.Set.t } 
             deriving (Show,Compare)
  let compare = Compare_t.compare
  let format = Show_t.format
  let show = Show_t.show

  let equal l1 l2 = (l1.par == l2.par) &&
                    (AP.Set.equal l1.acq l2.acq) &&
                    (AP.Set.equal l1.rel l2.rel)
  let unit = { par = Pos;
               acq = AP.Set.empty;
               rel = AP.Set.empty }
  let neg l = { l with par = if l.par == Pos then Neg else Pos }
  let mul l1 l2 = match (l1.par, l2.par) with
    | (Pos, Neg)
    | (Neg, Pos) -> { par = Pos;
                      acq = AP.Set.inter l1.acq l2.acq;
                      rel = AP.Set.empty }
    | _          ->
        let remove eq l rel = 
          AP.Set.filter (fun x -> not (AP.Set.exists (eq x) rel)) l
        in 
          { par = Pos;
            acq = AP.Set.union (remove Pa.may_alias l1.acq l2.rel) l2.acq;
            rel = AP.Set.union (remove AP.equal l1.rel l2.acq) l2.rel }
  (* Not sure if this is the right way to handle existentials *)
  let subst sub_var l =
    let add iap set = match AP.psubst_var sub_var iap with
      | Some z -> AP.Set.add z set
      | None   -> set
    in
      { par = l.par;
        acq = AP.Set.fold add l.acq AP.Set.empty;
        rel = AP.Set.fold add l.rel AP.Set.empty }
  let hash l = Hashtbl.hash (Hashtbl.hash l.par, 
                             AP.Set.hash l.acq, 
                             AP.Set.hash l.rel)
  (* x implies y if x acquires a subset of y and releases a superset of y *)
  let implies sub x y =
    let sub_iap iap =
      match AP.psubst_var (fun x -> Some (sub x)) iap with
        | Some z -> z
        | None -> assert false (* impossible *) in
    let y_sub = { par = Pos;
                  acq = AP.Set.map sub_iap y.acq;
                  rel = AP.Set.map sub_iap y.rel }
    in
      (AP.Set.for_all (fun k -> AP.Set.mem k y_sub.acq) x.acq) &&
      (AP.Set.for_all (fun k -> AP.Set.mem k x.rel) y_sub.rel)

  let pred_weight def =
    let get_deref e = match e with 
      | AccessPath ap -> AP.Set.singleton (Deref (AccessPath ap))
      | AddrOf     ap -> AP.Set.singleton ap
      | _             -> AP.Set.empty
    in match def.dkind with
    | Builtin (Acquire e) -> { par = Pos;
                               acq = get_deref e;
                               rel = AP.Set.empty }
    | Builtin (Release e) -> { par = Pos;
                               acq = AP.Set.empty;
                               rel = get_deref e }
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
          | AccessPath ap 
          | AddrOf ap      -> assume hack (AP.free_vars ap) pw
          | _              -> failwith ("Lock logic: Acquired non-access path: " ^ (Def.show def))
        end
      | Release e -> begin match e with
          | AccessPath ap 
          | AddrOf ap      -> assume hack (AP.free_vars ap) pw
          | _              -> failwith ("Lock logic: Released non-access path: " ^ (Def.show def))
        end
      | Alloc (v, e, targ) -> assign (Variable v) (Havoc (Var.get_type v)) pw
      | Free _             
      | Fork (_, _, _)
      | AtomicBegin       
      | AtomicEnd          -> one
      | Exit               -> zero
    in match def.dkind with
      | Assign (v, e)        -> assign (Variable v) e pw
      | Store  (a, e)        -> assign a e pw
      | Call   (vo, e, elst) -> failwith "Lock logic: Call encountered"
      | Assume be          
      | Assert (be, _)       -> assume be (Bexpr.free_vars be) pw
      | AssertMemSafe (e, s) -> assume (Bexpr.of_expr e) (Expr.free_vars e) pw
      | Initial              -> one 
      | Return eo            -> failwith "Lock logic: Return encountered"
      | Builtin bi -> weight_builtin bi
end

module LockPath = MakePath(LockPred)

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
  let mul_r pd lp =
    let zero_lp = zero_locks lp in
      M.map (fun lp -> LockPath.mul lp zero_lp) pd
  let mul_l lp pd = M.map (fun lp' -> LockPath.mul lp lp') pd
  let exists f pd = M.map (fun lp -> LockPath.exists f lp) pd
end

(* Fork maps *)
module FM = struct
  include Mapped(Def)(PD)
  type var = Var.t

  let equal = M.equal PD.equal
  let join = merge PD.join
  let mul_r a lp = M.map (fun f -> PD.mul_r f lp) a
  let mul_l lp a = M.map (fun f -> PD.mul_l lp f) a
  let exists f a = M.map (fun g -> PD.exists f g) a
  let absorb a pd = M.map (PD.join pd) a
end

(* Domain for the data race analysis *)
module Domain = struct
  type var = Var.t
  type t = { lp : LockPath.t;
             seq : PD.t;
             con : PD.t * PD.t;
             frk : FM.t }
             deriving(Show,Compare)
  let compare = Compare_t.compare
  let format = Show_t.format
  let show = Show_t.show

  let mp f (a1, a2) (b1, b2) = (f a1 b1, f a2 b2)

  let equal a b = (LockPath.equal a.lp b.lp) && 
                  (PD.equal a.seq b.seq) &&
                  (PD.equal (fst a.con) (fst b.con)) &&
                  (PD.equal (snd a.con) (snd b.con)) &&
                  (FM.equal a.frk b.frk)
  let mul a b =
    let aseq = PD.mul_r a.seq b.lp in
    let bseq = PD.mul_l a.lp b.seq in
      { lp = LockPath.mul a.lp b.lp;
        seq = PD.join aseq bseq;
        con = mp PD.join a.con b.con;
        frk = FM.join (FM.absorb (FM.mul_r a.frk b.lp) bseq) (FM.mul_l a.lp b.frk) }
  let add a b = { lp = LockPath.add a.lp b.lp;
                  seq = PD.join a.seq b.seq;
                  con = mp PD.join a.con b.con;
                  frk = FM.join a.frk b.frk }
  let zero = { lp = LockPath.zero;
               seq = PD.bot;
               con = (PD.bot, PD.bot);
               frk = FM.bot } 
  let one = { lp = LockPath.one;
              seq = PD.bot;
              con = (PD.bot, PD.bot);
              frk = FM.bot }
  let star a = 
    let l = LockPath.star a.lp in
      { lp = l; 
        seq = PD.mul_l l (PD.mul_r a.seq l);
        con = a.con;
        frk = FM.mul_l l (FM.mul_r a.frk l) }
  let exists f a = { lp = LockPath.exists f a.lp;
                     seq = PD.exists f a.seq;
                     con = (PD.exists f (fst a.con),
                            PD.exists f (snd a.con));
                     frk = FM.exists f a.frk }
end

module Datarace = struct
  module LSA = Interproc.MakePathExpr(Domain)
  open Domain


  let get_func e = match Expr.strip_all_casts e with
    | AccessPath (Variable (func, voff)) -> func
    | AddrOf     (Variable (func, voff)) -> func
    | _  -> failwith "Lock Logic: Called/Forked expression not a function"

  (* The weight function needs a map from initial nodes to a list of fork
   * points (to pass definitions from parent to child), a hash table of 
   * summaries (to pass definitions from a child to a parent), and a weight
   * function for lockpath (so that the equality logic can be stabilized *)
  let weight fmap sums wt def = 
    let fpoints =
      try Def.HT.find_all fmap def
      with Not_found -> []
    in
    let lsum = 
      let f a (b, v) =
        try let summary = LSA.HT.find sums b in
            let lval = FM.M.find v summary.frk in
              PD.join a lval
        with Not_found -> a
      in
        (List.fold_left f PD.bot fpoints, PD.bot)
    in
      match def.dkind with
        | Call (vo, e, elst) ->
            begin 
              try LSA.HT.find sums (get_func e)
              with Not_found -> one 
            end
        | Builtin (Fork (vo, e, elst)) -> 
            let summary =
              try LSA.HT.find sums (get_func e)
              with Not_found -> one
            in
              { lp = LockPath.one; 
                seq = PD.bot;
                con = (PD.bot, PD.join summary.seq (snd summary.con));
                frk = FM.M.add def PD.bot FM.M.empty }
        | Assign (v, e) -> 
            let l = wt def in
              { lp = l;
                seq = PD.M.add v l PD.M.empty;
                con = (PD.bot, PD.bot);
                frk = FM.bot }
        | _ -> { lp = wt def;
                 seq = PD.bot;
                 con = lsum;
                 frk = FM.bot }

  let may_race path v = 
    try 
      let defs = PD.M.find v (PD.join (fst path.con) (snd path.con)) in
      let sub  = LockPath.Minterm.subst (fun x -> if Var.get_subscript x = 1
                                                  then Var.subscript x 3
                                                  else x)
      in
      let fold_con seq_path con_path acc =
        let con_path' = sub
          (LockPath.Minterm.make (LockPath.Minterm.get_eqs con_path)
                                 (LockPred.neg (LockPath.Minterm.get_pred con_path)))
        in
        let l = LockPath.Minterm.get_pred (LockPath.Minterm.mul seq_path con_path') in
          acc || AP.Set.is_empty l.LockPred.acq
      in
      let fold_seq seq_path acc = 
        acc || LockPath.fold_minterms (fold_con seq_path) defs false
      in
        LockPath.fold_minterms fold_seq path.lp false
    with Not_found -> false

  let find_all_races query vlst =
    let classify v = match v.dkind with
      | Builtin (Fork (vo, e, elst)) -> RecGraph.Block (get_func e)
      | _ -> Interproc.V.classify v
    in
    let ht = Def.HT.create 32 in
    let f (block, def, path) =
      let races = Var.Set.filter (fun v -> may_race path v) vlst
      in
        print_endline (Def.show def ^ " ---- " ^  Domain.show path);
        Def.HT.add ht def races
    in
      BatEnum.iter f (LSA.enum_single_src_tmp classify query);
      ht

  (* Given wt, a transition formula over lock logic and some predicates,
   * construct a stabilized transition formula *)
  let stabilise races wt def =
    let pre =
      let frame = try Def.HT.find races def with Not_found -> Var.Set.empty in
        LockPath.of_minterm frame (LockPath.Minterm.make [] LockPred.unit)
    in
    let post =
      let frame = try Def.HT.find races def with Not_found -> Var.Set.empty in
        LockPath.of_minterm frame (LockPath.Minterm.make [] LockPred.unit)
    in
      LockPath.mul pre (LockPath.mul (wt def) post)

  let eq_races r1 r2 = 
    let f k v s = s && List.exists (Var.Set.equal v) (Def.HT.find_all r1 k) in
      Def.HT.fold f r2 true

  let init file =
    match file.entry_points with
    | [main] -> begin
      let rg = Interproc.make_recgraph file in
      let fmap = 
        let ht = Def.HT.create 32 in
        let f (b, v) = match v.dkind with
          | Builtin (Fork (vo, e, elst)) -> 
              Def.HT.add ht (Interproc.RG.block_entry rg (get_func e)) (b, v)
          | _ -> ()
        in 
          begin
            BatEnum.iter f (Interproc.RG.vertices rg);
            ht
          end
      in
      let local func_name =
        let func = lookup_function func_name (get_gfile()) in
        let vars = Varinfo.Set.remove (return_var func_name)
                     (Varinfo.Set.of_enum (BatEnum.append (BatList.enum func.formals)
                                                          (BatList.enum func.locals)))
        in
          fun (x, _) -> (Varinfo.Set.mem x vars)
      in
      (* Adds edges to the callgraph for each fork. Shouldn't really have to do
       * this every time a new query is made *)
      let add_fork_edges q =
        let f (b, v) = match v.dkind with
          | Builtin (Fork (vo, e, elst)) -> LSA.add_callgraph_edge q b (get_func e)
          | _ -> ()
        in
          BatEnum.iter f (Interproc.RG.vertices rg)
      in
      let compute_races races =
        let l_weight = stabilise races LockPath.weight in
        let rec iter_query old_query = 
          let eq sum1 sum2 = 
            let f k v s = s && List.exists (Domain.equal v) (LSA.HT.find_all sum1 k) in
              LSA.HT.fold f sum2 true
          in
          let new_query = 
            LSA.mk_query rg (weight fmap (LSA.get_summaries old_query) l_weight)
              local main
          in
            begin
              add_fork_edges new_query;
              LSA.compute_summaries new_query;
              if eq (LSA.get_summaries old_query) 
                    (LSA.get_summaries new_query)
              then new_query
              else iter_query new_query
            end
        in
        let initial =
          LSA.mk_query rg (weight fmap (LSA.HT.create 0) l_weight) local main
        in
          add_fork_edges initial;
          LSA.compute_summaries initial;
          find_all_races (iter_query initial) 
            (List.fold_left (fun acc -> fun vi -> Var.Set.add (Var.mk vi) acc) Var.Set.empty file.vars)
      in
      let rec fp_races old_races =
        let new_races = compute_races old_races in
        (*let f def v = print_endline ((Def.show def) ^ " --> " ^ (Var.Set.show v)) in
          Def.HT.iter f new_races;*)
          if eq_races old_races new_races then new_races
                                          else fp_races new_races
      in
      let init_races = 
        let ht = Def.HT.create 32 in
          List.iter (fun func -> 
            CfgIr.Cfg.iter_vertex (fun def -> Def.HT.add ht def Var.Set.empty) func.cfg)
          file.funcs;
          ht
      in
        BatEnum.iter (fun (_, g) -> Interproc.RGD.display g) (Interproc.RG.bodies rg);
        fp_races init_races
      end
    | _      -> assert false
end
(*
let analyze file = 
  let dra = Datarace.init file in
  let f def = 
    let g v = print_endline ((Var.show v) ^ " :: " ^ (string_of_bool (Datarace.may_race dra v def)))
    in
      print_endline (Def.show def);
      Var.Set.iter g (Def.free_vars def)
  in
    List.iter (fun func -> CfgIr.Cfg.iter_vertex f func.cfg) file.funcs
 *)
let analyze file = 
  let dra = Datarace.init file in
  let f def v = print_endline ((Def.show def) ^ " --> " ^ (Var.Set.show v)) in
    Def.HT.iter f dra

let _ =
  CmdLine.register_pass
    ("-dra", analyze, " Data race analysis")
