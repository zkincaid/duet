(*pp camlp4find deriving.syntax *)

open Core
open CfgIr
open Apak

(* -----------------Domains *)
module type Predicate = sig
  include EqLogic.Hashed.Predicate
  val pred_weight : Def.t -> t
end

module LockPred = struct
  type t = { acq : AP.Set.t;
             rel : AP.Set.t } 
             deriving (Show,Compare)
  type var = Var.t
  let compare = Compare_t.compare
  let format = Show_t.format
  let show = Show_t.show

  let equal l1 l2 = (AP.Set.equal l1.acq l2.acq) &&
                    (AP.Set.equal l1.rel l2.rel)
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
          | _              -> failwith ("Lock logic: Acquired non-access path: " ^ (Def.show def))
        end
      | Release e -> begin match e with
          | AccessPath ap  -> assume hack (AP.free_vars ap) pw
          | AddrOf ap      -> assume hack (AP.free_vars ap) pw
          | _              -> failwith ("Lock logic: Released non-access path: " ^ (Def.show def))
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
      | Call   (vo, e, elst) -> failwith "Lock logic: Call encountered"
      | Assume be            -> assume be (Bexpr.free_vars be) pw
      | Assert (be, s)       -> assume be (Bexpr.free_vars be) pw
      | AssertMemSafe (e, s) -> assume (Bexpr.of_expr e) (Expr.free_vars e) pw
      | Initial              -> one 
      | Return eo            -> failwith "Lock logic: Return encountered"
      | Builtin bi -> weight_builtin bi
end

module LockPath = MakePath(LockPred)

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

module Test = Interproc.MakePathExpr(Domain)

let get_func e = match Expr.strip_all_casts e with
  | AccessPath (Variable (func, voff)) -> func
  | AddrOf     (Variable (func, voff)) -> func
  | _  -> failwith "Lock Logic: Called/Forked expression not a function"

let fork_classify d = match d.dkind with
  | Builtin (Fork (vo, e, elst)) -> Some (get_func e)
  | _                            -> None

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
      (List.fold_left f PD.bot fpoints, PD.bot)
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
              seq = PD.bot;
              con = (PD.bot, PD.join summary.seq (snd summary.con));
              frk = FM.M.add def PD.bot FM.M.empty }
      | Assign (v, e) -> 
          let l = LockPath.weight def in
            { lp = l;
              seq = PD.M.add v l PD.M.empty;
              con = (PD.bot, PD.bot);
              frk = FM.bot }
      | _ -> { lp = LockPath.weight def;
               seq = PD.bot;
               con = lsum;
               frk = FM.bot }

let may_race v d =
  try 
    let defs = PD.M.find v (PD.join (fst d.Domain.con) (snd d.Domain.con)) in
    let fold_con seq_path con_path acc =
      let l = LockPath.Minterm.get_pred seq_path in
      let l' = LockPath.Minterm.get_pred con_path in
        (* We check the intersection. Likely the correct thing to do is check
         * whether the intersection of the relevant equivalence classes
         * is empty *)
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
    let rg = Interproc.make_recgraph file in
    let fmap = 
      let ht = Def.HT.create 32 in
      let f (b, v) = match v.dkind with
        | Builtin (Fork (vo, e, elst)) -> Def.HT.add ht (Interproc.RG.block_entry rg (get_func e)) (b, v)
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
      in fun (x, _) -> (Varinfo.Set.mem x vars) in
    let add_fork_edges q =
      let f (b, v) = match fork_classify v with
        | Some b' -> Test.add_callgraph_edge q b' b
        | None    -> ()
      in
        BatEnum.iter f (Interproc.RG.vertices rg)
    in
    let sum_eq sum1 sum2 = 
      let f k v s = s && List.exists (Domain.equal v) (Test.HT.find_all sum1 k) in
        Test.HT.fold f sum2 true in
    let rec iter_query old_query = 
      let new_query = Test.mk_query rg (weight fmap (Test.get_summaries old_query)) local main in
        begin
          add_fork_edges new_query;
          Test.compute_summaries new_query;
          if sum_eq (Test.get_summaries old_query) (Test.get_summaries new_query)
            then new_query
            else iter_query new_query 
        end in
    let query =
      let q = (Test.mk_query rg (weight fmap (Test.HT.create 0)) local main) in
        begin
          add_fork_edges q;
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
                                        print_endline (Domain.show
                                         (Test.single_src query main v))
                                  end)
                   (Interproc.RG.vertices rg);
      flush stdout
    end
  | _      -> assert false

let _ =
  CmdLine.register_pass
    ("-dra", analyze, " Data race analysis")
