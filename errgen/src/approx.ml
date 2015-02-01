open Ast
open Apak
open Ark
open ArkPervasives
open BatPervasives
open Syntax
open Cfa

include Log.Make(struct let name = "errgen" end)
module K = Syntax.K
module T = K.T
module F = K.F
module V = K.V
module D = T.D

let absolute_value term =
  let abs = V.mk_tmp "abs" TyReal in
  let at = T.var abs in
  (abs,
   F.conj
     (F.conj (F.leq term at) (F.leq (T.neg term) at))
     (F.disj (F.eq term at) (F.eq (T.neg term) at)))

(* Template intervals *)
module TIvl = struct
  module M = Putil.Map.Make(T)
  module I = Ark.Interval
  type t = I.interval M.t

  let compare = M.compare I.compare
  let equal = M.equal I.equal

  let abstract templates phi =
    let bounds = F.optimize templates phi in
    BatList.fold_left2 (fun m k v -> M.add k v m) M.empty templates bounds

  let top templates =
    BatList.fold_left (fun m t -> M.add t I.top m) M.empty templates

  let bottom templates =
    BatList.fold_left (fun m t -> M.add t I.top m) M.empty templates

  let join =
    let f _ a b = match a,b with
      | Some a, Some b -> Some (I.join a b)
      | Some a, None | None, Some a -> Some a (* Should really be None... *)
      | None, None -> None
    in
    M.merge f

  let widen =
    let f _ a b = match a,b with
      | Some a, Some b -> Some (I.widen a b)
      | Some a, None | None, Some a -> Some a (* Should really be None... *)
      | None, None -> None
    in
    M.merge f

  let meet =
    let f _ a b = match a,b with
      | Some a, Some b -> Some (I.meet a b)
      | Some a, None | None, Some a -> Some a
      | None, None -> None
    in
    M.merge f

  let to_formula prop =
    let ti_formula (template, ivl) =
      let lower = match Interval.lower ivl with
        | Some lo -> F.leq (T.const lo) template
        | None -> F.top
      in
      let upper = match Interval.upper ivl with
        | Some hi -> F.leq template (T.const hi)
        | None -> F.top
      in
      F.conj lower upper
    in
    (M.enum prop /@ ti_formula) |> F.big_conj

  let nudge = M.map (I.nudge ~accuracy:3)

  let abstract_post tr prop =
    let phi =
      F.linearize
        (fun () -> V.mk_tmp "nonlin" TyReal)
        (F.conj (K.to_formula tr) (to_formula prop))
    in
    let unprime =
      K.M.enum tr.K.transform
      /@ (fun (v,_) -> (Var.prime v, T.var (V.mk_var v)))
      |> K.M.of_enum
    in
    let old =
      K.VarMemo.memo
        (fun v -> T.var (V.mk_tmp ((Var.show v) ^ "_old") (Var.typ v)))
    in
    let sigma x = match V.lower x with
      | Some v ->
        if K.M.mem v unprime then K.M.find v unprime
        else if K.M.mem v tr.K.transform then old v
        else T.var x
      | None -> T.var x
    in
    let phi = F.subst sigma phi in
    let templates = BatList.of_enum (M.keys prop) in
    let bounds = F.optimize templates phi in
    BatList.fold_left2 (fun m k v -> M.add k v m) M.empty templates bounds
    |> nudge

  let format formatter prop =
    Format.fprintf formatter "[|@[";
    M.iter (fun template ivl ->
        let lo = match I.lower ivl with
          | Some lo -> QQ.show lo
          | None -> "-oo"
        in
        let hi = match I.upper ivl with
          | Some hi -> QQ.show hi
          | None -> "+oo"
        in
        Format.fprintf formatter "@[%s <= %a <= %s@]@\n"
          lo
          T.format template
          hi
      ) prop;
    Format.fprintf formatter "@]|]"
  let is_bottom = M.exists (fun _ ivl -> I.equal ivl I.bottom)
end

type magic
module AbstractDomain = struct
  type t = magic D.t option
  include Putil.MakeFmt(struct
      type a = t
      let format formatter = function
        | Some x -> D.format formatter x
        | None -> Format.pp_print_string formatter "_|_"
    end)
  let join x y = match x,y with
    | Some x, Some y -> Some (D.join x y)
    | Some x, None | None, Some x -> Some x
    | None, None -> None
  let widen x y = match x,y with
    | Some x, Some y -> Some (D.widen x y)
    | Some x, None | None, Some x -> Some x
    | None, None -> None
  let bottom = None
  let equal x y = match x,y with
    | Some x, Some y -> D.equal x y
    | None, None -> true
    | _, _ -> false
  let lower man = function
    | Some x -> x
    | None -> D.bottom man D.Env.empty
  let lift f = function
    | Some x -> Some (f x)
    | None -> None
end
module A = Fixpoint.MakeAnalysis(Cfa)(AbstractDomain)

module CfaPathexp = Pathexp.MakeElim(Cfa)(Syntax.K)


let post_formula tr =
  let phi =
    F.linearize
      (fun () -> V.mk_tmp "nonlin" TyReal)
      (K.to_formula tr)
  in
  let unprime =
    K.M.enum tr.K.transform
    /@ (fun (v,_) -> (Var.prime v, T.var (V.mk_var v)))
    |> K.M.of_enum
  in
  let old =
    K.VarMemo.memo
      (fun v -> T.var (V.mk_tmp ((Var.show v) ^ "_old") (Var.typ v)))
  in
  let sigma x = match V.lower x with
    | Some v ->
      if K.M.mem v unprime then K.M.find v unprime
      else if K.M.mem v tr.K.transform then old v
      else T.var x
    | None -> T.var x
  in
  F.subst sigma phi


(* Analyze floating & real program separately; annotation for a tensor node
     (u,v) is the conjunction of the (floating) annotation at u with the
     (real) annoation at v.  *)
let analyze_sep (approx,approx_entry) (ideal,ideal_entry) =
  let man = Box.manager_of_box (Box.manager_alloc ()) in
  let property_formula prop = F.of_abstract (AbstractDomain.lower man prop) in
  let analyze cfa entry =
    let vertex_tr v prop =
      if v = entry then Some (D.top man D.Env.empty) else prop
    in
    let tr e =
      AbstractDomain.lift (fun prop -> K.abstract_post man (Cfa.E.label e) prop)
    in
    let result =
      A.analyze_ldi vertex_tr ~edge_transfer:tr ~delay:3 ~max_decrease:2 cfa
    in
    let annotation = A.output result in
    let pe =
      let weight e =
        K.mul
          (K.assume (property_formula (annotation (Cfa.E.src e))))
          (Cfa.E.label e)
      in
      CfaPathexp.single_src cfa weight ideal_entry
    in
    let pe_annotation = Memo.memo (fun u -> post_formula (pe u)) in
    (pe_annotation, cfa)
  in
  let (approx_annotation, approx_cfa) = analyze approx approx_entry in
  let (ideal_annotation, ideal_cfa) = analyze ideal ideal_entry in
  ((fun (u, v) ->
      F.conj (approx_annotation u) (ideal_annotation v)),
   ideal_cfa,
   approx_cfa)


module P = Pathexp.MakeElim(TCfa)(K)

(* Aux function for Chebyshev distance: given an enumeration of terms, returns
   a pair (d, phi) consisting of a (fresh) variable d and a formula phi such
   that that the formula implies that the variable is the maximum of the
   absolute values of all the terms (so if terms is an enumeration of all
   differences "x' - x", then the variable is constrained to by the chebyshev
   distance. *)
let chebyshev terms =
  let d = V.mk_tmp "dist" TyReal in
  let terms = BatEnum.append terms (BatEnum.map T.neg (BatEnum.clone terms)) in
  let ub = F.big_conj (BatEnum.map (F.geq (T.var d)) (BatEnum.clone terms)) in
  let eq = F.big_disj (BatEnum.map (F.eq (T.var d)) terms) in
  (d, F.conj ub eq)

(* Aux function for Manhattan distance (see chebyshev) *)
let manhattan terms =
  let d = V.mk_tmp "dist" TyReal in
  let (abs_vars, abs_cons) =
    BatEnum.uncombine (BatEnum.map absolute_value terms)
  in
  let abs_terms = BatEnum.map T.var abs_vars in
  (d, F.conj (F.big_conj abs_cons) (F.eq (T.var d) (T.sum abs_terms)))

let forall p phi = F.negate (F.qe_lme p (F.negate phi))

let greedy annotation vars approx_tr ideal_tr ideal_succs =
  let open BatPervasives in

  let ideal_succs = K.normalize ideal_succs in
  let get_transform v tr =
    try K.M.find v tr.K.transform
    with Not_found -> T.var (V.mk_var v)
  in

  (* Distance between the post-state of approx_tr and ideal_tr *)
  let (dist, dist_cons) =
    let terms =
      let diff v =
        T.sub
          (get_transform (idealify v) ideal_tr)
          (get_transform (approxify v) approx_tr)
      in
      BatEnum.map diff (BatList.enum vars)
    in
    chebyshev terms
  in

  (* Distance between the post-state of approx_tr and ideal_succs *)
  let (other_dist, other_dist_cons) =
    let terms =
      let diff v =
        T.sub
          (get_transform (idealify v) ideal_succs)
          (get_transform (approxify v) approx_tr)
      in
      BatEnum.map diff (BatList.enum vars)
    in
    chebyshev terms
  in

  (* ideal_tr minimizes post-state distance *)
  let dist_guard =
    let phi = (* other_dist_cons => dist - other_dist <= eps_0 *)
      F.big_disj (BatList.enum [
          F.negate ideal_succs.K.guard;
          F.negate other_dist_cons;
(*
          F.negate annotation;
          F.negate approx_tr.K.guard;
*)
          (F.leq (T.sub (T.var dist) (T.var other_dist)) (T.const eps_0))
        ])
    in
    let approx_temps = K.formula_free_tmp_vars (K.to_formula approx_tr) in
    let p v =
      not_tmp v || K.VSet.mem v approx_temps || V.equal v dist
    in
    let res =
      Log.time "forall-elim" (forall p) phi
    in

(*    logf "res: %a@\n" F.format (F.qe_lme (fun _ -> true) res);*)
(*
    logf "ideal: %a@\n" F.format ideal_succs.K.guard;
    logf "approx: %a@\n" F.format approx_tr.K.guard;
    logf "annotation: %a@\n" F.format annotation;
*)
(*
    logf "before elim: %a@\n" F.format (F.flatten
                                          (F.qe_lme (fun _ -> true) 
                                             (F.big_conj (BatList.enum [
                                                  ideal_succs.K.guard;
                                                  approx_tr.K.guard;
                                                  annotation]))));
    *)
    res
  in
  (*  logf "Dist guard: %a" F.format dist_guard;*)
  let guard =
    F.big_conj (BatList.enum [
        dist_guard;
        approx_tr.K.guard;
        ideal_tr.K.guard;
        dist_cons;
        annotation
      ])
  in
  logf "Dist_cons: %a@\n" F.format (F.boxify [T.var dist] guard);
  let add_transform v t tr = K.M.add v t tr in
  { K.guard = guard;
    K.transform = K.M.fold add_transform approx_tr.K.transform ideal_tr.K.transform }

(* Maps a vertex v to a transition which approximates the transition relation
   starting at v (and going anywhere) *)
let tr_succs cfa =
  let f e tr = K.add (Cfa.E.label e) tr in
  Memo.memo (fun v -> Cfa.fold_succ_e f cfa v K.zero)

type ctx =
  { annotation : int * int -> F.t;
    tr_succs : int -> K.t;
    vars : string list;
    approx_cfa : Cfa.t;
    ideal_cfa : Cfa.t }

let tensor_edge ctx =
  Memo.memo (fun ((a_src,i_src),(a_dst,i_dst)) ->
      logf "Computing tensor edge (%d,%d) -> (%d,%d)"
        a_src i_src
        a_dst i_dst;
      let e1 = Cfa.find_edge ctx.approx_cfa a_src a_dst in
      let e2 = Cfa.find_edge ctx.ideal_cfa i_src i_dst in
      let tr1 = Cfa.E.label e1 in
      let tr2 = Cfa.E.label e2 in
      let succs = ctx.tr_succs (Cfa.E.src e2) in
      let res =
        Log.time "tensor_edge"
          (greedy (ctx.annotation (a_src,i_src)) ctx.vars tr1 tr2) succs
      in
(*
      logf "Computed tensor edge (%d,%d) -> (%d,%d):@\n%a"
        a_src i_src
        a_dst i_dst
        K.format res;
*)
      res)

module Worklist = struct
  include Putil.Set.Make(struct
      type t = int * int deriving (Show,Compare)
      let compare = Compare_t.compare
      let show = Show_t.show
      let format = Show_t.format
    end)
end

module TemplateSet = Putil.Set.Make(T)
let templates_of_prop man prop =
  let open Apron in
  let open Tcons0 in
  let f xs lc =
    let t =
      match T.to_linterm (T.of_apron prop.D.env lc.texpr0) with
      | None -> assert false
      | Some lt ->
        T.Linterm.sub lt (T.Linterm.const (T.Linterm.const_coeff lt))
        |> T.of_linterm
    in
    TemplateSet.add t xs
 in
 Array.fold_left f TemplateSet.empty (Abstract0.to_tcons_array man prop.D.prop)

let tivl_widen man templates upper x y =
  let discovered =
    TemplateSet.inter (templates_of_prop man x) (templates_of_prop man y)
  in
  let templates =
    TemplateSet.union
      discovered
      (TemplateSet.of_enum (BatList.enum templates))
    |> TemplateSet.elements
  in
  logf "TIvl widening discovered templates: %a" TemplateSet.format discovered;
  let tivl_of_prop = TIvl.abstract templates % F.of_abstract in
  let res =
    TIvl.widen (tivl_of_prop x) (tivl_of_prop y)
    |> TIvl.meet (TIvl.abstract templates upper)
    |> TIvl.to_formula
    |> F.abstract man
  in
  logf "-->%a" D.format res;
  res

let attractor_bounds ctx tensor_edge =
  let mk_var = T.var % V.mk_var in
  let diff v =
    T.sub (mk_var (idealify v)) (mk_var (approxify v))
  in
  let differences = List.map diff ctx.vars in
  let templates =
    List.map mk_var ctx.vars
    @ List.map (mk_var % approxify) ctx.vars
  in

  let src = TCfa.E.src tensor_edge in
  let dst = TCfa.E.dst tensor_edge in

  let tr = TCfa.E.label tensor_edge in
  let postify v =
    try K.M.find v tr.K.transform
    with Not_found -> T.var (V.mk_var v)
  in
  let bounds x =
    let pre_diff =
      T.sub (T.var (V.mk_var (idealify x))) (T.var (V.mk_var (approxify x)))
    in
    let post_diff =
      T.sub (postify (idealify x)) (postify (approxify x))
    in
    let phi =
      F.big_conj (BatList.enum [
          tr.K.guard;
          F.geq pre_diff T.zero; (* positive *)
          F.geq post_diff pre_diff (* increasing *)
        ])
    in
    let psi =
      F.big_conj (BatList.enum [
          tr.K.guard;
          F.leq pre_diff T.zero; (* negative *)
          F.leq post_diff pre_diff (* decreasing *)
        ])
    in
    let pi_bounds = List.hd (F.optimize [post_diff] phi) in
    let nd_bounds = List.hd (F.optimize [post_diff] psi) in
    Interval.join pi_bounds nd_bounds
  in
  let res =
    List.fold_left2
      (fun m diff bounds -> TIvl.M.add diff bounds m)
      TIvl.M.empty
      differences
      (List.map bounds ctx.vars) 
  in
  logf ~attributes:[Log.Magenta] "Outward bounds %a -> %a: %a"
    Show.format<int*int> src
    Show.format<int*int> dst
    TIvl.format res;
  TIvl.meet res (TIvl.abstract templates (ctx.annotation dst))

(*
let build_sync_tensor ctx entry =
  Cfa.fold_edges_e (fun approx_edge tensor ->
      let ideal_edge =
        Cfa.find_edge ctx.ideal_cfa (Cfa.E.src approx_edge) (Cfa.E.dst approx_edge)
      in
      let tensor_edge =
        Log.time "tensor_edge" (tensor_edge ctx approx_edge) ideal_edge
      in
      TCfa.add_edge_e tensor tensor_edge
    ) ctx.approx_cfa (TCfa.add_vertex TCfa.empty entry)
*)

let analyze ctx approx_entry ideal_entry =
  let entry = (approx_entry, ideal_entry) in
  let annotation = Hashtbl.create 991 in (* annotation table *)
  let delay_widening = Hashtbl.create 991 in
  let tensor_edge = tensor_edge ctx in
  let attractor_bounds = attractor_bounds ctx in

  let templates =
    let mk_var = T.var % V.mk_var in
    let diff v =
      T.sub (mk_var (idealify v)) (mk_var (approxify v))
    in
    List.map mk_var ctx.vars
    @ List.map (mk_var % approxify) ctx.vars
    @ List.map diff ctx.vars
  in
  let sep_annotation = ctx.annotation in
  let man = NumDomain.polka_loose_manager () in

  let ctx = { ctx with annotation =
                         fun v ->
                           try
                             F.conj
                               (F.of_abstract (Hashtbl.find annotation v))
                               (ctx.annotation v)
                           with Not_found -> assert false }
  in
  let tensor = ref (TCfa.add_vertex TCfa.empty entry) in
  let worklist = ref (Worklist.singleton entry) in
  let is_cutpoint = ref (fun _ -> false) in
  let pop_worklist () =
    let (v, wl) = Worklist.pop (!worklist) in
    worklist := wl;
    v
  in

  let check_edge ctx precondition e =
    let src = TCfa.E.src e in
    let approx_dst = fst (TCfa.E.dst e) in
    let f e k =
      if fst (TCfa.E.dst e) = approx_dst then K.add k (TCfa.E.label e)
      else k
    in
    let outgoing = TCfa.fold_succ_e f (!tensor) src K.zero in
    let is_primed v =
      v.[String.length v - 1] = '''
      || (v.[String.length v - 1] = '^' && v.[String.length v - 2] = ''')
    in
    let p v = match V.lower v with
      | Some v -> is_primed v
      | None -> false
    in
    let outgoing_phi =
      let make_eq v =
        let v = approxify v in
        let post = T.var (V.mk_var (Var.prime v)) in
        F.eq post (try K.M.find v outgoing.K.transform
                   with Not_found -> T.var (V.mk_var v))
      in
      F.conj (F.big_conj (BatList.enum ctx.vars /@ make_eq)) outgoing.K.guard
    in

    let s = new Smt.solver in
    s#assrt (F.to_smt precondition);
    s#assrt (F.to_smt (F.qe_lme p (K.to_formula (TCfa.E.label e))));
    s#assrt (F.to_smt (F.negate (F.qe_lme not_tmp outgoing_phi)));
    match s#check () with
    | Smt.Sat   ->
      (logf "model@\n%s" (((s#get_model())#to_string()));
       true)
    | Smt.Unsat -> false
    | Smt.Undef -> assert false
  in
  let check_edge ctx precondition e =
    Log.time "check_edge" (check_edge ctx precondition) e
  in

  let add_edge e =
    let src = TCfa.E.src e in
    let dst = TCfa.E.dst e in
    if TCfa.mem_edge (!tensor) src dst then
      begin
        tensor := TCfa.remove_edge (!tensor) src dst;
        logf ~attributes:[Log.Red;Log.Bold] "Updated edge: %a -> %a"
          Show.format<int*int> src
          Show.format<int*int> dst
      end
    else
      begin
        logf ~attributes:[Log.Red;Log.Bold] "New edge: %a -> %a"
          Show.format<int*int> src
          Show.format<int*int> dst;
      end;
    tensor := TCfa.add_edge_e (!tensor) e;
    is_cutpoint := TL.is_header (TL.construct (!tensor))
  in

  let precondition =
    BatList.enum ctx.vars
    /@ (fun v ->
        F.eq (T.var (V.mk_var (approxify v))) (T.var (V.mk_var (idealify v))))
    |> F.big_conj
    |> F.abstract man
  in
  Hashtbl.add annotation entry precondition;

  while not (Worklist.is_empty (!worklist)) do
    let (approx_v, ideal_v) = pop_worklist () in
    let precondition =
      try Hashtbl.find annotation (approx_v, ideal_v)
      with Not_found -> assert false
    in
    logf ~attributes:[Log.Green]
      "=-=-=-=-  Forward iteration @@ (%d, %d) -=-=-=-=" approx_v ideal_v;
    logf "Precondition: %a" D.format precondition;
    logf "TIVL: %a" TIvl.format (TIvl.abstract templates (F.of_abstract precondition));

    (* Recompute outgoing edges *)
    let f approx_edge =
      let g ideal_edge =
        let source = (Cfa.E.src approx_edge, Cfa.E.src ideal_edge) in
        let target = (Cfa.E.dst approx_edge, Cfa.E.dst ideal_edge) in

        let tensor_tr = tensor_edge (source, target) in
        let tensor_edge =
          TCfa.E.create source tensor_tr target
        in
        let post =
          Log.time "abstract_post"
            (K.abstract_post man tensor_tr) precondition
        in

        if not (D.is_bottom post)
        && (TCfa.mem_edge (!tensor) source target
            || check_edge ctx (F.of_abstract precondition) tensor_edge)
        then
          begin
            add_edge tensor_edge;
            logf "Post --> %a" D.format post;
            try
              let new_annotation =
                let old_prop = Hashtbl.find annotation target in
                let delay =
                  try Hashtbl.find delay_widening target
                  with Not_found -> begin
                      Hashtbl.add delay_widening target 0;
                      0
                    end
                in
                Hashtbl.replace delay_widening target (delay + 1);
                if delay >= 2 then
                  let attractor = attractor_bounds tensor_edge in
                  D.meet
                    (D.join
                       (D.join old_prop post)
                       (F.abstract man (TIvl.to_formula attractor)))
                    (tivl_widen man templates (sep_annotation target) old_prop post)
                else if delay >= 4 then
                  tivl_widen man templates (sep_annotation target) old_prop post
                else
                  D.join old_prop post
              in
              if not (D.equal (Hashtbl.find annotation target) new_annotation)
              then begin
                Hashtbl.replace annotation target new_annotation;
                worklist := Worklist.add target (!worklist)
              end
            with Not_found ->
              if not (D.is_bottom post) then begin
                logf ~attributes:[Log.Red;Log.Bold] "New reachable vertex: %a"
                  Show.format<int*int> target;

                Hashtbl.add annotation target post;
                worklist := Worklist.add target (!worklist)
              end else
                logf ~attributes:[Log.Blue;Log.Bold] "Redundant edge: %a -> %a"
                  Show.format<int*int> (TCfa.E.src tensor_edge)
                  Show.format<int*int> (TCfa.E.dst tensor_edge)
          end
      in
      let succs = Cfa.succ_e ctx.ideal_cfa ideal_v in
      let (x,y) = BatList.partition ((=) (Cfa.E.dst approx_edge) % Cfa.E.dst) succs in
      List.iter g x
      (*(x@y)*)
    in
    Cfa.iter_succ_e f ctx.approx_cfa approx_v
  done;

  let diff v =
    T.sub (T.var (V.mk_var (idealify v))) (T.var (V.mk_var (approxify v)))
  in
  let print_diff v bounds =
    let bound_str =
      match Interval.lower bounds, Interval.upper bounds with
      | (Some x, Some y) ->
        string_of_float (Mpqf.to_float (QQ.max (Mpqf.abs x) (Mpqf.abs y)))
      | (_, _) -> "oo"
    in
    Format.printf "  | %s - %s' | <= %s@\n" v v bound_str
  in
  let print_entry vtx prop =
    Format.printf "Distance at %a:@\n" Show.format<int*int> vtx;
    List.iter2 print_diff
      ctx.vars
      (F.optimize (List.map diff ctx.vars) (F.of_abstract prop))
  in
  Hashtbl.iter print_entry annotation

let usage_msg = "Usage: approx [OPTIONS] <ideal> <approx>\n"
                ^ "       approx [OPTIONS] -float <file>"

let ideal = ref None
let approx = ref None


let parse_file filename weight =
  let infile = Pervasives.open_in filename in
  let lexbuf = Lexing.from_channel infile in
  let Prog prog = Parser.main Lexer.token lexbuf in
  Pervasives.close_in infile;
  build_cfa prog weight

let anon_fun s =
  match !ideal, !approx with
  | None, _ -> ideal := Some (parse_file s real_weight)
  | Some _, None -> approx := Some (parse_file s (real_weight % primify_cmd))
  | _, _ -> failwith "Too many input files"

let float_arg =
  let set_float s =
    if !ideal == None && !approx == None then begin
      ideal := Some (parse_file s real_weight);
      approx := Some (parse_file s (float_weight % primify_cmd))
    end else
      failwith "Too many input files"
  in
  ("-float",
   Arg.String set_float,
   " Set approximate program to be floating point implementation")

let verbose_arg =
  ("-verbose",
   Arg.String (fun v -> Log.set_verbosity_level v Log.info),
   " Raise verbosity for a particular module")

let verbose_list_arg =
  ("-verbose-list",
   Arg.Unit (fun () ->
       print_endline "Available modules for setting verbosity:";
       Hashtbl.iter (fun k _ ->
           print_endline (" - " ^ k);
         ) Log.loggers;
       exit 0;
     ),
   " List modules which can be used with -verbose")

let spec_list = [
  float_arg;
  verbose_arg;
  verbose_list_arg
]

let _ =
  Arg.parse (Arg.align spec_list) anon_fun usage_msg;
  ArkPervasives.opt_default_accuracy := 5;
  F.opt_simplify_strategy := [F.qe_lme];
  match !ideal, !approx with
  | Some (ideal_cfa, ideal_entry, ideal_exit),
    Some (approx_cfa, approx_entry, approx_exit) ->
    begin
      let ideal_cfa = reduce_cfa ideal_cfa ideal_entry ideal_exit in
      let approx_cfa = reduce_cfa approx_cfa approx_entry approx_exit in

      let (annotation, ideal_cfa, approx_cfa) =
        analyze_sep (approx_cfa, approx_entry) (ideal_cfa, ideal_entry)
      in
      let ideal_cfa = normalize (add_stuttering (collapse_assume ideal_cfa)) in
      let approx_cfa = normalize (collapse_assume approx_cfa) in
      let ctx =
        { annotation = annotation;
          tr_succs = tr_succs ideal_cfa;
          vars = Cfa.collect_vars ideal_cfa;
          approx_cfa = approx_cfa;
          ideal_cfa = ideal_cfa }
      in
      analyze ctx approx_entry ideal_entry;
      Log.print_stats ()
    end
  | _, _ -> print_endline usage_msg
