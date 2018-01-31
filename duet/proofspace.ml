open Apak
open BatPervasives
open Core
open Srk
open Srk.Syntax
open Pa

include Log.Make(struct let name = "proofspace" end)

let tr_typ typ =
  match resolve_type typ with
  | Int _   -> `TyInt
  | Float _ -> `TyReal
  | Pointer _ -> `TyInt
  | Enum _ -> `TyInt
  | Array _ -> `TyInt
  | Dynamic -> `TyInt
  | _ -> `TyInt

module PInt = Putil.PInt
module Ctx = Syntax.MakeSimplifyingContext ()
module Atomicity = Dependence.AtomicityAnalysis

let ctx = Ctx.context
let smt_ctx = SrkZ3.mk_context ctx []

(* Indexed variables -- variables paired with thread identifiers *)
module IV = struct
  module I = struct
    type t = Var.t * int [@@deriving ord]

    let pp formatter (var, i) =
      if Var.is_shared var then Var.pp formatter var
      else Format.fprintf formatter "%a[#%d]" Var.pp var i

    let show = SrkUtil.mk_show pp

    let equal x y = compare x y = 0
    let hash (v, i) = Hashtbl.hash (Var.hash v, i)
  end
  include I

  let typ = tr_typ % Var.get_type % fst

  module Memo = Memo.Make(I)
  module Set = BatSet.Make(I)
  module HT = BatHashtbl.Make(I)

  let sym_to_var = Hashtbl.create 991
  let var_to_sym = HT.create 991

  let symbol_of var =
    if HT.mem var_to_sym var then
      HT.find var_to_sym var
    else begin
        let sym = Ctx.mk_symbol ~name:(show var) (typ var) in
        HT.add var_to_sym var sym;
        Hashtbl.add sym_to_var sym var;
        sym
      end

  let of_symbol sym =
    if Hashtbl.mem sym_to_var sym then
      Some (Hashtbl.find sym_to_var sym)
    else
      None
end

module P = struct
  type t = Ctx.formula
  let equal = Formula.equal
  let compare = Formula.compare
  let hash = Formula.hash
  let pp = Formula.pp ctx
  let conjuncts phi =
    match Formula.destruct ctx phi with
    | `And conjuncts -> BatList.enum conjuncts
    | `Tru -> BatEnum.empty ()
    | _ -> BatEnum.singleton phi
  let big_conj enum = Ctx.mk_and (BatList.of_enum enum)
  let big_disj enum = Ctx.mk_or (BatList.of_enum enum)
  let constants phi =
    fold_constants
      (fun sym set ->
        match IV.of_symbol sym with
        | Some v -> IV.Set.add v set
        | None -> set)
      phi
      IV.Set.empty
end

module Tr = Transition.Make(Ctx)(IV)

module Block = struct
  type t =
    [ `Fork of Varinfo.t
    | `Initial
    | `Transition of Tr.t ]
      [@@deriving ord]

  let equal a b = compare a b = 0

  let pp formatter block = match block with
    | `Initial -> Format.pp_print_string formatter "Initial"
    | `Fork thread -> Format.fprintf formatter "fork(%a)" Varinfo.pp thread
    | `Transition tr -> Tr.pp formatter tr

  let show x = SrkUtil.mk_show pp x

  let default = `Transition Tr.one
end

module G = ExtGraph.Persistent.Digraph.MakeBidirectionalLabeled(PInt)(Block)

module ThreadCount = struct
  type t = int option [@@deriving ord,show]
  type var = unit
  let equal x y = compare x y = 0
  let exists _ x = x
  let one = Some 0
  let zero = Some 0
  let add x y = match x, y with
    | Some x, Some y -> Some (max x y)
    | _, _ -> None
  let mul x y = match x, y with
    | Some x, Some y -> Some (x + y)
    | _, _ -> None
  let star x = match x with
    | Some 0 -> Some 0
    | _ -> None
  let widen x y = match x, y with
    | Some 0, x | x, Some 0 -> x
    | Some x, Some y when x = y -> Some x
    | _, _ -> None
  let fork = function
    | Some k -> Some (k + 1)
    | None -> None
end
module TCA = Interproc.MakeParPathExpr(ThreadCount)

module Letter = struct
  include G.E
  let equal x y = compare x y = 0
  let hash edge = Hashtbl.hash (src edge, dst edge)
  let pp formatter edge = Block.pp formatter (label edge)
  let block = label
  let transition_of index e =
    match label e with
    | `Fork _ | `Initial -> Tr.one
    | `Transition tr ->
      let reindex sym =
        match IV.of_symbol sym with
        | None -> Ctx.mk_const sym
        | Some (v, i) ->
          if Var.is_shared v then
            Ctx.mk_const sym
          else
            Ctx.mk_const (IV.symbol_of (v, index))
      in
      let assign =
        Tr.transform tr
        /@ (fun ((v, i), term) ->
            let term = substitute_const ctx reindex term in
            if Var.is_shared v then
              ((v,i), term)
            else
              ((v,index), term))
        |> BatList.of_enum
      in
      Tr.construct
        (substitute_const ctx reindex (Tr.guard tr))
        assign

  let is_local e =
    match label e with
    | `Fork _ | `Initial -> false
    | `Transition tr ->
      let has_globals expr =
        fold_constants (fun sym global ->
            global
            || (match IV.of_symbol sym with
                | Some (v, _) when Var.is_shared v -> true
                | _ -> false))
          expr
          false
      in
      not (has_globals (Tr.guard tr)
           || BatEnum.exists
                (fun ((v,_), term) -> Var.is_shared v || (has_globals term))
                (Tr.transform tr))

  let is_transition e =
    match label e with
    | `Transition _ -> true
    | _ -> false

  module Set = BatSet.Make(G.E)
  module Map = BatMap.Make(G.E)
end

type block_graph =
  { graph : G.t; (* graph containing control flow graph of all threads *)
    initial : int Varinfo.Map.t; (* map each thread to its initial vertex *)
    mhp : Letter.Set.t PInt.Map.t; (* may happen in parallel *)
    error : int (* designated error vertex *) }

module PA = PredicateAutomata.Make
    (Letter)
    (struct
      include P
      let pp formatter p = Format.fprintf formatter "{%a}" pp p
    end)

module E = PredicateAutomata.MakeEmpty(PA)

(* Negate a PA formula.  Atoms are left unchanged, predicates in the resulting
   formula should be interpreted negatively.  negate_paformula is only applied
   to the right hand side of transitions in PAs corresponding to proof
   spaces. *)
let negate_paformula =
  let open PaFormula in
  PaFormula.eval (function
      | `T -> mk_false
      | `F -> mk_true
      | `Atom (predicate, terms) -> mk_atom predicate terms
      | `And (phi, psi) -> mk_or phi psi
      | `Or (phi, psi) -> mk_and phi psi
      | `Forall (name, body) -> mk_exists ~name body
      | `Exists (name, body) -> mk_forall ~name body
      | `Eq (s, t) -> mk_neq s t
      | `Neq (s, t) -> mk_eq s t)

(* Determine the arity of a predicate (i.e., the number of distinct threads
   whose local variables appear in the predicate).  This function assumes
   that expressions are "normal" in the sense that thread id's have been
   renamed to occupy an initial segment of the naturals. *)
let arity phi =
  let f m (v, idx) =
    if Var.is_shared v then m else max m idx
  in
  BatEnum.fold f 0 (IV.Set.enum (P.constants phi))

(* not_assign is a set of all definitions which are not assignments.  assign
   maps each variable to the set of definitions which assign to it *)
type assign_table =
  { alphabet : Letter.Set.t;
    assign : Letter.Set.t Var.Map.t }

let get_assign v table =
  try Var.Map.find v table.assign
  with Not_found -> Letter.Set.empty

let make_assign_table alphabet =
  let assign =
    Letter.Set.fold (fun letter assign ->
        match Letter.block letter with
        | `Initial | `Fork _ -> assign
        | `Transition tr ->
          BatEnum.fold (fun assign ((v, _), _) ->
              let letters =
                try
                  Letter.Set.add letter (Var.Map.find v assign)
                with Not_found ->
                  Letter.Set.singleton letter
              in
              Var.Map.add v letters assign)
            assign
            (Tr.transform tr))
      alphabet
      Var.Map.empty
  in
  { alphabet; assign }

let is_stable letter assertion =
  let program_vars = P.constants assertion in
  let unindexed_program_vars =
    IV.Set.enum program_vars /@ fst |> Var.Set.of_enum
  in
  match Letter.block letter with
  | `Initial | `Fork _ -> true
  | `Transition tr ->
    BatEnum.for_all (fun ((v, _), _) ->
        not (Var.Set.mem v unindexed_program_vars))
      (Tr.transform tr)

(* Given an assertion phi, add transitions corresponding to Hoare triples of
   the form { phi } tr { phi }, where tr does not assign to any variable in
   phi. *)
let add_stable solver assign_table assertion =
  let program_vars = P.constants assertion in
  let unindexed_program_vars =
    IV.Set.enum program_vars /@ fst |> Var.Set.of_enum
  in
  let arity = arity assertion in
  let stable =
    PaFormula.mk_atom
      assertion
      (BatList.of_enum ((1 -- arity) /@ (fun i -> PaFormula.Var i)))
  in

  (* Add stable transition for definitions which do not write to any variable
     that appears in assertion *)
  let (unstable, local_unstable) =
    let (global_unstable, local_unstable) =
      Var.Set.fold (fun v (local, global) ->
          if Var.is_shared v then
            (local, Letter.Set.union global (get_assign v assign_table))
          else
            (Letter.Set.union local (get_assign v assign_table), global))
        unindexed_program_vars
        (Letter.Set.empty, Letter.Set.empty)
    in
    let unstable =
      Letter.Set.union global_unstable local_unstable
    in
    (unstable,
     Letter.Set.diff local_unstable global_unstable)
  in

  E.conjoin_transition
    solver
    assertion
    (Letter.Set.diff assign_table.alphabet unstable)
    (negate_paformula stable);

  (* Add conditional stable transitions for definitions that write to local
     variables that appear in the assertion *)
  local_unstable |> Letter.Set.iter (fun letter ->
      let tr = match Letter.block letter with
        | `Transition tr -> tr (* only block transitions may be unstable *)
        | _ -> assert false
      in
      let rhs =
        let index_set =
          IV.Set.enum program_vars |> BatEnum.fold (fun set (v, i) ->
              if Tr.mem_transform (v, 0) tr then
                PInt.Set.add i set
              else
                set)
            PInt.Set.empty
        in
        let open PaFormula in
        PInt.Set.fold (fun i rhs ->
            mk_and rhs (mk_neq (Var 0) (Var i)))
          index_set
          stable
      in
      E.conjoin_transition
        solver
        assertion
        (Letter.Set.singleton letter)
        (negate_paformula rhs))

let gensym typ = Ctx.mk_const (Ctx.mk_symbol ~name:"havoc" typ)

(* Convert a Core IR expression into a term.  Local variables are interpreted
   as the locals of tid. *)
let index_expr index =
  let alg = function
    | OHavoc typ -> gensym (tr_typ typ)
    | OConstant (CInt (k, _)) -> Ctx.mk_real (QQ.of_int k)
    | OConstant (CFloat (k, _)) -> Ctx.mk_real (QQ.of_float k)
    | OCast (_, expr) -> expr
    | OBinaryOp (a, Add, b, _) -> Ctx.mk_add [a; b]
    | OBinaryOp (a, Mult, b, _) -> Ctx.mk_mul [a; b]
    | OBinaryOp (a, Minus, b, _) -> Ctx.mk_sub a b

    | OUnaryOp (Neg, a, _) -> Ctx.mk_neg a

    | OAccessPath (Variable v) -> Ctx.mk_const (IV.symbol_of (v, index))

    (* No real translations for anything else -- just return a free var "tr"
       (which just acts like a havoc). *)
    | OBinaryOp (a, _, b, typ) -> gensym (tr_typ typ)
    | OUnaryOp (_, _, typ) -> gensym (tr_typ typ)
    | OBoolExpr _ -> gensym `TyInt
    | OAccessPath ap -> gensym (tr_typ (AP.get_type ap))
    | OConstant _ -> gensym `TyInt
    | OAddrOf _ -> gensym `TyInt
  in
  Aexpr.fold alg

(* Convert a Core IR boolean expression into a formula.  Local variables are
   interpreted as the locals of tid. *)
let index_bexpr tid =
  let alg = function
    | OAnd (a, b) -> Ctx.mk_and [a; b]
    | OOr (a, b) -> Ctx.mk_or [a; b]
    | OAtom (pred, x, y) ->
      let x = index_expr tid x in
      let y = index_expr tid y in
      begin
        match pred with
        | Lt -> Ctx.mk_lt x y
        | Le -> Ctx.mk_leq x y
        | Eq -> Ctx.mk_eq x y
        | Ne -> Ctx.mk_not (Ctx.mk_eq x y)
      end
  in
  Bexpr.fold alg

let generalize i phi psi =
  let generalize_atom phi =
    let subst = BatDynArray.make 10 in
    let rev_subst = BatHashtbl.create 31 in
    let generalize i =
      try BatHashtbl.find rev_subst i
      with Not_found -> begin
          let id = BatDynArray.length subst in
          BatHashtbl.add rev_subst i id;
          BatDynArray.add subst i;
          id
        end
    in
    let sigma sym =
      match IV.of_symbol sym with
      | Some (v, tid) ->
        let iv =
          if Var.is_shared v then (v, tid) else (v, 1 + generalize tid)
        in
        Ctx.mk_const (IV.symbol_of iv)
      | None -> assert false
    in
    let gen_phi = substitute_const ctx sigma phi in
    (gen_phi, BatDynArray.to_list subst)
  in
  let subst = BatDynArray.make 10 in
  let rev_subst = BatHashtbl.create 31 in
  BatDynArray.add subst i;

  let generalize i =
    try BatHashtbl.find rev_subst i
    with Not_found -> begin
        let id = BatDynArray.length subst in
        BatHashtbl.add rev_subst i id;
        BatDynArray.add subst i;
        id
      end
  in
  let sigma sym =
    match IV.of_symbol sym with
    | Some (v, tid) ->
      let iv =
        if Var.is_shared v then (v, tid) else (v, generalize tid)
      in
      Ctx.mk_const (IV.symbol_of iv)
    | None -> assert false
  in
  let gen_phi = substitute_const ctx sigma phi in
  let f psi =
    let (gen_psi, args) = generalize_atom psi in
    PaFormula.mk_atom
      gen_psi
      (List.map (fun i -> PaFormula.Var (generalize i)) args)
  in
  let mk_eq ((i,j), (k,l)) =
    let open PaFormula in
    if i = k then
      mk_eq (Var j) (Var l)
    else
      mk_neq (Var j) (Var l)
  in
  BatHashtbl.add rev_subst i 0;
  let rhs =
    let props = BatList.of_enum (BatEnum.map f (P.conjuncts psi)) in
    let vars = BatHashtbl.enum rev_subst in
    PaFormula.big_conj
      (BatEnum.append
         (BatList.enum props)
         (SrkUtil.distinct_pairs vars /@ mk_eq))
  in
  (subst, gen_phi, rhs)

(* Given an infeasible trace, construct Hoare triples proving its
   infeasibility and add corresponding *negated* transitions to the PA
   solver. *)
let construct_interp solver assign_table trace =
  let rec go trace itp post =
    match trace, itp with
    | ((letter, tid)::trace, pre::itp) ->
      let letters = Letter.Set.singleton letter in
      let pre = rewrite ctx ~down:(nnf_rewriter ctx) pre in
      if P.compare pre post = 0 then begin
        Log.logf "Skipping transition: [#%d] %a" tid Letter.pp letter;
        let (_, lhs, rhs) = generalize tid post pre in
        let lhs_arity = arity lhs in
        if not (E.mem_vocabulary solver lhs) then begin
          E.add_accepting_predicate solver lhs lhs_arity;
          add_stable solver assign_table lhs
        end;
        if not (is_stable letter post) then
          E.conjoin_transition solver lhs letters (negate_paformula rhs);
        go trace itp pre
      end else begin
        begin match BatList.of_enum (P.conjuncts pre) with
          | [] -> ()
          | [pre] -> go trace itp pre
          | preconditions ->
            (* if the interpolant is a non-trivial conjunction, process each
               conjunct separately *)
            let transitions =
              List.rev_map
                (fun (letter, tid) -> Letter.transition_of tid letter)
              trace
            in
            preconditions |> List.iter (fun pre ->
                let itp =
                  match Tr.interpolate transitions pre with
                  | `Valid itp -> List.tl (List.rev itp)
                  | _ -> Log.fatalf "Failed to interpolate!"
                in
                go trace itp pre)
        end;
        let (_, lhs, rhs) = generalize tid post pre in
        let lhs_arity = arity lhs in
        if not (E.mem_vocabulary solver lhs) then begin
          E.add_accepting_predicate solver lhs lhs_arity;
          add_stable solver assign_table lhs
        end;
        Log.logf
          "Added PA transition:@\n @[{%a}(%a)@]@\n --( [#0] %a )-->@\n @[%a@]"
          P.pp lhs
          (SrkUtil.pp_print_enum Format.pp_print_int) (1 -- lhs_arity)
          Letter.pp letter
          PA.pp_formula rhs;
        E.conjoin_transition solver lhs letters (negate_paformula rhs)
      end

    | x, y -> assert (x = [] && y = [])
  in
  let transitions =
    List.map (fun (letter, tid) -> Letter.transition_of tid letter) trace
  in
  match Tr.interpolate transitions Ctx.mk_false with
  | `Valid itp -> go (List.rev trace) (List.tl (List.rev itp)) Ctx.mk_false
  | _ -> Log.fatalf "Failed to interpolate!"

(* Construct a proofspace from the trace given a strategy for producing
   symbolic hoare triples.
   add_triples : Solver.t -> (letter, tid) list -> (letter, tid) list
 *)
module Solver = Hoare.MakeSolver(Ctx)(IV)
let construct solver assign_table trace add_triples =
  let hoare_solver = Solver.mk_solver () in
  let trace = List.filter (fun (letter, tid) -> Tr.compare (Letter.transition_of tid letter) Tr.one != 0) trace in
  let rec go trace triples =
    match trace, triples with
    | (letter, tid) :: trace, (pre, trans, post) :: triples ->
       let mk_conj phi =
         let rec flatten phi =
           List.fold_left (fun conj psi -> match (destruct ctx psi) with
                                           | `And psi -> List.append conj (flatten psi)
                                           | _ -> List.append conj [psi]) [] phi
         in
         match phi with
         | [] -> Ctx.mk_true
         | [phi] -> rewrite ctx ~down:(nnf_rewriter ctx) phi
         | phi -> Ctx.mk_and (flatten (List.rev_map (rewrite ctx ~down:(nnf_rewriter ctx)) phi))
       in
       let letters = Letter.Set.singleton letter in
       let pre = mk_conj pre in
       let post = mk_conj post in
       (*Log.logf ~level:`always "%a" Solver.pp_triple ([pre], trans, [post]);*)
       List.iter (fun psi ->
           let (_, psi, rhs) = generalize tid psi pre in
           let psi_arity = (arity psi) in
           if not (E.mem_vocabulary solver psi) then begin
               E.add_accepting_predicate solver psi psi_arity;
               add_stable solver assign_table psi
             end;
           if P.compare pre post != 0 || not (is_stable letter post) then begin
               logf
                 "Added PA transition:@\n @[{%a}(%a)@]@\n --( [#0] %a )-->@\n @[%a@]"
                 P.pp psi
                 (SrkUtil.pp_print_enum Format.pp_print_int) (1 -- psi_arity)
                 Letter.pp letter
                 PA.pp_formula rhs;
               E.conjoin_transition solver psi letters (negate_paformula rhs)
             end
         ) ((BatList.of_enum  (P.conjuncts post)));
       go trace triples
    | x, y -> assert (x = [] && y = [])
  in
  let trace = add_triples hoare_solver trace in
  match Solver.check_solution hoare_solver with
  | `Sat -> go trace (Solver.get_solution hoare_solver)
  | _ -> Log.fatalf "Failed to find hoare triples"

let construct_sequence solver assign_table trace =
  let add_triples hoare_solver trace =
    let transitions =
      List.map (fun (letter, tid) -> Letter.transition_of tid letter) trace
    in
    let vars =
      IV.Set.to_list
        (List.fold_left (fun vars trans ->
           List.fold_left (fun vars var -> IV.Set.add var vars) vars (Tr.defines trans)
           ) IV.Set.empty transitions)
    in
    let vars_type  = List.map IV.typ vars in
    let vars_const = List.map (fun var -> Ctx.mk_const (IV.symbol_of var)) vars in
    let get_pred var_types =
      Ctx.mk_symbol (`TyFun (var_types, `TyBool))
    in
    let rec go pre transitions =
      match transitions with
      | trans :: [] -> Solver.register_triple hoare_solver ([pre], trans, [Ctx.mk_false])
      | trans :: transitions ->
         begin
           let post = Ctx.mk_app (get_pred vars_type) vars_const in
           (*logf "%a" Solver.pp_triple ([pre], trans, [post]);*)
           Solver.register_triple hoare_solver ([pre], trans, [post]);
           go post transitions
         end
      | [] -> assert false
    in go Ctx.mk_true transitions; trace
  in
  construct solver assign_table trace add_triples

let construct_loop solver assign_table trace =
  let add_triples hoare_solver trace =
    let transitions =
      List.map (fun (letter, tid) -> Letter.transition_of tid letter) trace
    in
    let vars =
      IV.Set.to_list
        (List.fold_left (fun vars trans ->
           List.fold_left (fun vars var -> IV.Set.add var vars) vars (Tr.defines trans)
           ) IV.Set.empty transitions)
    in
    let vars_type  = List.map IV.typ vars in
    let vars_const = List.map (fun var -> Ctx.mk_const (IV.symbol_of var)) vars in
    let module DA = BatDynArray in
    let locs = (* Compute Initial Location for each thread *)
      DA.init ((List.fold_left (fun max (_, tid) -> if max > tid then max else tid) 0 trace) + 1)
              (fun i -> match (try Some (List.find (fun (_, tid) -> tid == i) trace) with
                               | _ -> None) with
                        | None -> -1
                        | Some (letter, _) -> Letter.src letter)
    in
    let get_pred var_types =
      Memo.memo (fun _ -> Ctx.mk_symbol (`TyFun (var_types, `TyBool))) (* each location product gets a single relation symbol *)
    in
    let get_pred = get_pred vars_type in
    let rec go pre trace =
      match trace with
      | (letter, tid) :: [] -> Solver.register_triple hoare_solver ([pre], (Letter.transition_of tid letter), [Ctx.mk_false])
      | (letter, tid) :: trace ->
         begin
           DA.set locs tid (Letter.dst letter);
           let post = Ctx.mk_app (get_pred (DA.to_list locs)) vars_const in
           Solver.register_triple hoare_solver ([pre], (Letter.transition_of tid letter), [post]);
           go post trace
         end
      | [] -> assert false
    in go Ctx.mk_true trace; trace
  in
  construct solver assign_table trace add_triples
  
(*
let construct_owici_gries solver assign_table trace =
  let add_triples hoare_solver trace =
    let transitions =
      List.map (fun (letter, tid) -> Letter.transition_of tid letter) trace
    in
    let module DA = BatDynArray in
    let vars =
      let locals = DA.init ((List.fold_left (fun max (_, tid) -> if max > tid then max else tid) 0 trace) + 1) (fun _ -> IV.Set.empty) in
      List.iter (fun trans ->
          List.iter (fun (var, tid) ->
              if Var.is_shared var then
                  DA.set locals 0 (IV.Set.add (var, tid) (DA.get locals 0))
              else
                begin
                  assert (tid != 0);
                  DA.set locals tid (IV.Set.add (var, tid) (DA.get locals tid))
                end
            ) (Tr.defines trans)) transitions;
      DA.map IV.Set.to_list locals
    in
    let vars_type  = DA.map (List.map IV.typ) vars in
    let vars_const = DA.map (List.map (fun var -> Ctx.mk_const (IV.symbol_of var))) vars in
    let preds = DA.init (DA.length vars) (fun _ -> []) in (* All relations per thread *)
    let get_pred var_types =
      Ctx.mk_symbol (`TyFun (var_types, `TyBool))
    in
    let letters = ref [] in
    let rec go trace =
      match trace with
      | [] -> ()
      | (letter, tid) :: trace ->
         begin
           let transition = Letter.transition_of tid letter in
           let var_types = List.append (DA.get vars_type tid) (DA.get vars_type 0) in
           let vars_const = List.append (DA.get vars_const tid) (DA.get vars_const 0) in
           let pre =
             match (DA.get preds tid) with
             | phi :: _ -> phi
             | [] -> Ctx.mk_true
           in
           let post = Ctx.mk_app (get_pred var_types) vars_const in
           Solver.register_triple hoare_solver ([pre], transition, [post]); (* Consecution *)
           letters := (letter, tid) :: (!letters);
           DA.set preds tid (post :: (DA.get preds tid)); (* Add post to history of relations for thread tid *)
           (* Non-interfereance triples *)
           DA.iteri (fun id preds -> if id != tid then List.iter
                                                         (fun phi -> letters := (letter, tid) :: (!letters);
                                                                     Solver.register_triple hoare_solver ([pre; phi], transition, [phi])) preds
                    ) preds;
           go trace
         end
    in
    go trace;
    let posts = DA.fold_left (fun posts phis -> match phis with
                                                | [] -> posts
                                                | phi :: _ -> (phi :: posts)) [] preds
    in
    Solver.register_triple hoare_solver (posts, Tr.one, [Ctx.mk_false]);
    !letters
     (* ((`Transition Tr.one), 0) :: !letters (* Should add epsilon transition, but how? this doesn't type check :( *) *)
  in
  construct solver assign_table trace add_triples
 *)      
let construct = construct_interp

let construct solver trace =
  Log.time "PA construction" (construct solver) trace

let mk_block_graph file =
  let rg = Interproc.remove_skip (Interproc.make_recgraph file) in
  let main = match file.CfgIr.entry_points with
    | [x] -> x
    | _   -> failwith "PA: No support for multiple entry points"
  in
  let block_of_def def =
    match def.dkind with
    | Assume phi ->
      `Transition (Tr.assume (index_bexpr 0 phi))
    | Assign (v, expr) ->
      `Transition (Tr.assign (v, 0) (index_expr 0 expr))
    | Builtin (Fork (_, expr, _)) ->
      let func = match Aexpr.strip_casts expr with
        | AddrOf (Variable (func, OffsetFixed 0)) -> func
        | _ -> assert false
      in
      `Fork func
    | _ ->
      `Transition (Tr.assume Ctx.mk_true)
  in
  let add_graph graph g = 
    Interproc.RG.G.fold_edges (fun u v g ->
        G.add_edge_e g (G.E.create u.did (block_of_def u) v.did))
      graph
      g
  in
  let fresh_id () = (Def.mk (Assume (Bexpr.ktrue))).did in
  let (graph, initial) =
    BatEnum.fold (fun (g, initial) (thread, body) ->
        let g = add_graph body g in
        let old_entry = (Interproc.RG.block_entry rg thread).did in
        let new_entry = fresh_id () in
        let g =
          G.add_edge_e g (G.E.create new_entry `Initial old_entry)
        in
        (g, Varinfo.Map.add thread new_entry initial))
      (G.empty, Varinfo.Map.empty)
      (Interproc.RG.bodies rg)
  in
  let error = -1 in
  
  let graph = (* add error transitions for asserts *)
    BatEnum.fold (fun g (_, def) ->
        match def.dkind with
      | Assert (phi, _) ->
        let block =
          `Transition (Tr.assume (Ctx.mk_not (index_bexpr 0 phi)))
        in
        G.add_edge_e g (G.E.create def.did block error)
      | _ -> g)
      graph
      (Interproc.RG.vertices rg)
  in

  let graph =
    (* Collapse non-loop, non-endpoint vertices such that either (1) all
       outgoing edges are local transitions (2) all incoming edges are local
       transitions. *)
    G.fold_vertex (fun v g ->
        let preds = G.pred_e g v in
        let succs = G.succ_e g v in
        if (not (G.mem_edge g v v) (* non-loop *)
            && List.length preds > 0 && List.length succs > 0 (* non-endpoint *)
            && ((List.for_all Letter.is_local succs
                 && List.for_all Letter.is_transition preds)
                || (List.for_all Letter.is_local preds
                    && List.for_all Letter.is_transition succs)))
        then
          List.fold_left (fun g pred ->
              List.fold_left (fun g succ ->
                  match Letter.label pred, Letter.label succ with
                  | `Transition tr, `Transition tr' ->
                    let mul_letter =
                      Letter.create
                        (Letter.src pred)
                        (`Transition (Tr.mul tr tr'))
                        (Letter.dst succ)
                    in
                    G.add_edge_e g mul_letter
                  | _, _ -> assert false)
                g
                succs)
            (G.remove_vertex g v)
            preds
        else
          g)
      graph
      graph
  in


  (* TODO: for correctness, all we need is to make sure that transitions of
     the main thread do not happen in parallel with each other and initial
     transitions don't happen in parallel with anything.  We might be able to
     get a significant reduction with a more accurate MHP analysis *)
  let mhp =
    let main_thread_vertices =
      Interproc.RG.G.fold_vertex (fun v vertices ->
          PInt.Set.add v.did vertices)
        (Interproc.RG.block_body rg main)
        PInt.Set.empty
    in
    let alphabet =
      BatEnum.fold
        (flip Letter.Set.add)
        Letter.Set.empty
        (G.edges_e graph)
    in
    let thread_letters =
      Letter.Set.filter
        (fun e -> not (PInt.Set.mem (Letter.src e) main_thread_vertices))
        alphabet
    in
    let mhp =
      G.fold_vertex (fun v mhp ->
          let mhp_letter =
            if PInt.Set.mem v main_thread_vertices then
              thread_letters
            else
              alphabet
          in
        PInt.Map.add v mhp_letter mhp)
        graph
        PInt.Map.empty
    in

    (* remove mhp entries for vertices within atomic sections *)
    let mhp =
      let open CfgIr in
      List.fold_left (fun mhp func ->
          let result =
            Atomicity.do_analysis func.cfg (fun _ -> None)
          in
          BatEnum.fold (fun mhp (v, level) ->
              match level with
              | Some lvl when lvl > 0 ->
                PInt.Map.add v.did Letter.Set.empty mhp
              | _ -> mhp)
            mhp
            (Atomicity.enum_output result))
        mhp
        file.funcs
    in

    (* remove mhp entries for initial vertices *)
    Varinfo.Map.fold (fun thread v mhp ->
        PInt.Map.add v Letter.Set.empty mhp)
      initial
      mhp
  in
  { graph; initial; mhp; error }

let program_automaton file =
  let open Interproc in
  let main = match file.CfgIr.entry_points with
    | [x] -> x
    | _   -> failwith "PA: No support for multiple entry points"
  in
  let block_graph = mk_block_graph file in

  (* Map each control location to a unique monadic predicate symbol *)
  let loc_pred =
    let pred = Ctx.mk_symbol ~name:"@" (`TyFun ([`TyInt], `TyBool)) in
    fun vertex ->
      Ctx.mk_app pred [Ctx.mk_real (QQ.of_int vertex)]
  in

  let init_vertex thread =
    try Varinfo.Map.find thread block_graph.initial
    with Not_found -> assert false
  in

  (* Nullary error predicate: asserts are replaced with guarded transitions to
     error. *)
  let err = Ctx.mk_const (Ctx.mk_symbol ~name:"err" `TyBool) in

  (* Nullary loc predicate ensures that whenever a new thread executes a
     command its program counter is instantiated properly. *)
  let loc = Ctx.mk_const (Ctx.mk_symbol ~name:"loc" `TyBool) in

  let alphabet =
    BatEnum.fold
      (flip Letter.Set.add)
      Letter.Set.empty
      (G.edges_e block_graph.graph)
  in
  let vocabulary =
    G.fold_vertex
      (fun v vocab -> (loc_pred v, 1)::vocab)
      block_graph.graph
      [(loc, 0); (err, 0)]
  in
  let initial_formula =
    PaFormula.mk_and (PaFormula.mk_atom loc []) (PaFormula.mk_atom err [])
  in
  let pa =
    PA.make
      alphabet
      vocabulary
      initial_formula
      [loc; loc_pred (init_vertex main)]
  in
  let add_single_transition lhs letter rhs =
    PA.add_transition pa lhs (Letter.Set.singleton letter) rhs
  in

  G.edges_e block_graph.graph |> BatEnum.iter (fun letter ->
      let src = Letter.src letter in
      let tgt = Letter.dst letter in
      let open PaFormula in

      begin match Letter.block letter with
        | `Fork thread ->
          (* delta(init-t(i), fork(t):j) = true *)
          add_single_transition (loc_pred (init_vertex thread)) letter mk_true
        | _ -> ()
      end;

      (* delta(err,sigma:i) = true *)
      if tgt = block_graph.error then
        add_single_transition err letter mk_true;

      (* delta(tgt(sigma)(i),sigma:j) = (i = j) *)
      add_single_transition (loc_pred tgt) letter (mk_eq (Var 0) (Var 1));

      (* delta(loc(),sigma:i) = loc /\ src(sigma)(i) *)
      add_single_transition loc letter (mk_and
                                          (mk_atom loc [])
                                          (mk_atom (loc_pred src) [Var 0])));

  (* delta(v(i), sigma:j) = v(i) /\ i != j *)
  G.vertices block_graph.graph |> BatEnum.iter (fun v ->
      let open PaFormula in
      let mhp = PInt.Map.find v block_graph.mhp in
      let v = loc_pred v in
      let rhs = mk_and (mk_atom v [Var 1]) (mk_neq (Var 0) (Var 1)) in
      PA.add_transition pa v mhp rhs);
  pa

let verify file =
  let open PA in
  Inline.inline_file file;
  let program_pa = program_automaton file in
  let assign_table = make_assign_table (alphabet program_pa) in

  let empty_proofspace_pa =
    PA.make
      (alphabet program_pa)
      [(Ctx.mk_false, 0)]
      (PaFormula.mk_atom Ctx.mk_false [])
      []
  in
  let max_index =
    (* redundant -- recgraph has already been computed *)
    let rg = Interproc.make_recgraph file in
    let main = match file.CfgIr.entry_points with
      | [x] -> x
      | _   -> failwith "PA: No support for multiple entry points"
    in
    let query = TCA.mk_query rg (fun _ -> Some 0) (fun _ _ -> true) main in
    match TCA.get_summary query main with
    | Some x ->
      logf "Found bound on number of threads: %d" x;
      x + 1
    | None ->
      logf "No static bound on number of threads";
      -1
  in

  (* { false } def { false } *)
  PA.add_transition
    empty_proofspace_pa
    Ctx.mk_false
    (alphabet program_pa)
    (PaFormula.mk_atom Ctx.mk_false []);

  let solver =
    E.mk_solver (PA.intersect program_pa (PA.negate empty_proofspace_pa))
  in

  let check () =
    Log.time "PA emptiness" (E.find_word ~max_index) solver
  in
  let number_cex = ref 0 in
  let print_info () =
    logf ~level:`info "  PA predicates: %d"
      (BatEnum.count (E.vocabulary solver));
    logf ~level:`info "  Spurious counter-examples: %d " !number_cex;
  in
  let rec loop () =
    match check () with
    | Some trace ->
      logf ~attributes:[`Bold] "@\nFound error trace (%d):" (!number_cex);
      List.iter (fun (letter, id) ->
          logf "  [#%d] %a" id Letter.pp letter
        ) trace;
      logf ""; (* newline *)
      let trace_formula =
        List.fold_right
          (fun (letter, index) tr ->
             Tr.mul (Letter.transition_of index letter) tr)
          trace
          Tr.one
        |> Tr.guard
      in
      begin
        match smt_ctx#is_sat trace_formula with
        | `Sat ->
          log ~level:`always ~attributes:[`Bold;`Red]
            "Verification result: Unsafe";
          print_info ();
          logf ~level:`info ~attributes:[`Bold] "  Error trace:";
          List.iter (fun (letter, id) ->
              logf ~level:`info "    [#%d] %a" id Letter.pp letter
            ) trace;
          logf ~level:`always "Embedding Queries %d" (PA.Config.num_queries ())
        | `Unsat ->
          construct solver assign_table trace;
          incr number_cex;
          loop ()
        | `Unknown ->
          log ~level:`always ~attributes:[`Bold;`Red]
            "Verification result: Unknown";
          print_info ();
          logf ~level:`info ~attributes:[`Bold] "  Could not verify trace:";
          List.iter (fun (letter, id) ->
              logf ~level:`info "    [#%d] %a" id Letter.pp letter
            ) trace;
          logf ~level:`always "Embedding Queries %d" (PA.Config.num_queries ())
      end
    | None ->
      log ~level:`always ~attributes:[`Bold;`Green]
        "Verification result: Safe";
      print_info ();
      logf ~level:`always "Embedding Queries %d" (PA.Config.num_queries ())
  in
  loop ()

let _ =
  CmdLine.register_pass
    ("-proofspace", verify, " Proof space");
  CmdLine.register_config
    ("-config-rep", Arg.String (function
         | "list" -> E.config_set_rep := `List
         | "feature-tree" -> E.config_set_rep := `FeatureTree
         | "predicate-tree" -> E.config_set_rep := `PredicateTree
         | s -> Log.errorf "Unknown option to -config-rep: `%s'" s),
     " Change representation of config sets (list, feature-tree, predicate-tree)");
  CmdLine.register_config
    ("-embed-algo", Arg.String (function
         | "match-embeds" -> E.embed_set_algo := `MatchEmbeds
         | "crypto-mini-sat" -> E.embed_set_algo := `CryptoMiniSat
         | "lingeling" -> E.embed_set_algo := `Lingeling
         | "haifa-csp" -> E.embed_set_algo := `HaifaCSP
         | "gecode" -> E.embed_set_algo := `Gecode
         | "or-tools" -> E.embed_set_algo := `OrTools
         | "vf2" -> E.embed_set_algo := `VF2
         | s -> Log.errorf "Unknown option to -embed-algo: `%s'" s),
     " Change embedding algorithm implementations (match-embeds, crypto-mini-sat, lingeling, haifa-csp, gecode, or-tools, vf2)")
