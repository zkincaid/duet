open Syntax
open Iteration
module V = Linear.QQVector
module M = Linear.QQMatrix
module Z = Linear.ZZVector
module H = Abstract
include Log.Make(struct let name = "srk.array:" end)

type 'a t = 'a formula

type qfp =  [ `Exists of string * Syntax.typ_fo
            | `Forall of string * Syntax.typ_fo ] list

let to_mfa srk phi =
  let combine deconstr_phis =
    let f (qf_pre0, boundbyuniv0, phi0) (eqf_pre, boundbyuniv, phis) =
      (* we remove the univ quantifiers and then add them back after this 
       * procedure; eqf_pre is the existential quantifier prefix. 
       * boundbyuniv is a boolean which is true when a univ quant
       * needs to be added. qf_pre0 still contains its univ quant;
       * bounbyuniv0 is redundant info specifying if univ quant
       * at head of qf_pre0. More complex optimizations
       * can be made to avoid introducing so many vars during disjunction *)
      if boundbyuniv0 = true && boundbyuniv = true
      then (
        let eqf_pre0 = List.tl (List.rev qf_pre0) in
        let depth = List.length eqf_pre  in 
        let depth0 = List.length eqf_pre0 in
        let phis = List.map (decapture srk (depth + 1) depth0) phis in
        (eqf_pre0@eqf_pre, true, (decapture srk 1 depth phi0)::phis)
      )
      else if boundbyuniv0 = true && boundbyuniv = false
      then (
        let eqf_pre0 = List.tl (List.rev qf_pre0) in
        let depth = List.length eqf_pre  in 
        let depth0 = List.length eqf_pre0 in 
        let phis = List.map (decapture srk 0 1) phis in
        let phis = List.map (decapture srk (depth + 1) depth0) phis in
        (eqf_pre0@eqf_pre, true, (decapture srk 1 depth phi0)::phis)
      )
      else if boundbyuniv0 = false && boundbyuniv = true
      then (
        let eqf_pre0 = qf_pre0 in
        let depth = List.length eqf_pre  in 
        let depth0 = List.length eqf_pre0 in 
        let phis = List.map (decapture srk (depth + 1) depth0) phis in
        (eqf_pre0@eqf_pre, true, (decapture srk 0 (depth + 1) phi0)::phis)
      )
      else
        (
          let eqf_pre0 = qf_pre0 in
          let depth = List.length eqf_pre  in 
          let depth0 = List.length eqf_pre0 in 
          let phis = List.map (decapture srk depth depth0) phis in
          (eqf_pre0@eqf_pre, false, (decapture srk 0 depth phi0)::phis)
        )
    in
    let eqf_pre, bbu, mat = List.fold_right f deconstr_phis ([], false, []) in
    let qf_pre = 
      if bbu then eqf_pre@[`Forall ("_", `TyInt)]
      else eqf_pre 
    in
    qf_pre, bbu, mat
  in
  let alg = function
    | `Tru -> ([], false, mk_true srk)
    | `Fls -> ([], false, mk_false srk)
    | `Atom (`Eq, x, y) -> ([], false, mk_eq srk x y)
    | `Atom (`Lt, x, y) -> ([], false, mk_lt srk x y)
    | `Atom (`Leq, x, y) -> ([], false, mk_leq srk x y)
    | `And deconstructed_conjuncts ->
      let (qf_pre, bbu, conjuncts_mat) = combine deconstructed_conjuncts in
      qf_pre, bbu, mk_and srk conjuncts_mat
    | `Or deconstructed_disjuncts ->
      let (qf_pre, bbu, disjuncts_mat) = combine deconstructed_disjuncts in
      if bbu = false then
        (qf_pre, bbu, mk_or srk disjuncts_mat)
      else 
        ((`Exists ("_", `TyInt)) :: qf_pre, 
         bbu, 
         mk_or 
           srk 
           (List.mapi 
              (fun ind disjunct_mat -> 
                 mk_and 
                   srk 
                   [disjunct_mat; 
                    mk_eq 
                      srk 
                      (mk_int srk ind)  
                      (mk_var srk (List.length qf_pre + 1) `TyInt)]) 
              disjuncts_mat))
    | `Quantify (`Exists, name, `TyInt, (qf_pre, bbu, phi)) ->
      (`Exists (name,`TyInt)::qf_pre, bbu, phi)
    | `Quantify (`Forall, name, `TyInt, (qf_pre, bbu, phi)) ->
      if bbu then failwith "not monic"
      else (`Forall (name, `TyInt)::qf_pre, true, phi)
    | `Quantify (_, _, _, _) -> failwith "quantifier over non-int sort" 
    | `Not (_, _, _) -> failwith "not positive"
    | `Proposition (`Var i) -> ([], false, mk_var srk i `TyBool) 
    | `Proposition (`App (p, args)) ->
      [], 
      false, 
      mk_app srk p (List.map (fun arg -> 
          begin match Expr.refine srk arg with 
            | `Term t -> t
            | `Formula _ -> failwith "TODO: formula in predicates"
          end)
          args)
    | `Ite (cond, bthen, belse) ->
      begin match combine [cond; bthen; belse] with
        | (qf_pre, bbu, [cond; bthen; belse]) ->
          (qf_pre, bbu, mk_ite srk cond bthen belse)
        | _ -> assert false
      end
  in
  let qf_pre, bbu, matrix = Formula.eval srk alg phi in
  qf_pre, bbu, matrix

let add_prefix srk (qf_pre, matrix) =
  List.fold_right
    (fun qf phi ->
       match qf with
       | `Exists (name, typ) -> mk_exists srk ~name typ phi
       | `Forall (name, typ) -> mk_forall srk ~name typ phi)
    qf_pre
    matrix

let mfa_to_lia srk (qfp, matrix) arruniv arrother bbu =
  let enumcounter = ref 0 in
  let arrunivcard = Symbol.Set.cardinal arruniv in
  let arrunivenum = Hashtbl.create arrunivcard in
  Symbol.Set.iter 
    (fun arrsym -> Hashtbl.add arrunivenum arrsym !enumcounter; 
      enumcounter := !enumcounter + 1) 
    arruniv;
  let innerqf = BatList.make arrunivcard (`Exists ("_", `TyInt)) in
  let qfp = qfp@innerqf in
  let matrix = decapture srk 0 arrunivcard matrix in
  let qfcounter = ref (List.length qfp) in
  let preqfmapsyms = Hashtbl.create (Symbol.Set.cardinal arrother) in
  let preqfmapvars = Hashtbl.create (Symbol.Set.cardinal arrother) in
  let rec termalg = function
    | `Real qq -> mk_real srk qq
    | `App (arrsym, [indvar]) -> 
      begin match destruct srk indvar with
        | `Var (ind, `TyInt) ->
          if ind = arrunivcard && bbu then
            mk_var srk (Hashtbl.find arrunivenum arrsym) `TyInt
          else
            begin match Hashtbl.find_opt preqfmapvars (arrsym, ind) with
              | Some existnum -> mk_var srk existnum `TyInt
              | None -> Hashtbl.add preqfmapvars (arrsym, ind) !qfcounter;
                qfcounter := !qfcounter + 1;
                mk_var srk (!qfcounter - 1) `TyInt
            end
        | `App (sym, []) -> 
          begin match Hashtbl.find_opt preqfmapsyms (arrsym, sym) with
            | Some existnum -> mk_var srk existnum `TyInt
            | None -> Hashtbl.add preqfmapsyms (arrsym, sym) !qfcounter;
              qfcounter := !qfcounter + 1;
              mk_var srk (!qfcounter - 1) `TyInt
          end
        | _ -> failwith "not flat"
      end
    | `App (f, args) ->
      mk_app 
        srk 
        f 
        (List.map (fun arg -> 
             begin match Expr.refine srk arg with 
               | `Term t -> ((Term.eval srk termalg t) :> ('a, typ_fo) expr)
               | `Formula f -> ((Formula.eval srk alg f) :> ('a, typ_fo) expr)
             end)
            args) 
    | `Var (i, `TyInt) -> mk_var srk i `TyInt
    | `Var (i, `TyReal) -> mk_var srk i `TyReal
    | `Add sum -> mk_add srk sum
    | `Mul product -> mk_add srk product
    | `Binop (`Div, s, t) -> mk_div srk s t
    | `Binop (`Mod, s, t) -> mk_mod srk s t
    | `Unop (`Floor, t) -> mk_floor srk t
    | `Unop (`Neg, t) -> mk_neg srk t
    | `Ite (cond, bthen, belse) -> 
      mk_ite 
        srk 
        (Formula.eval srk alg cond)
        (Term.eval srk termalg  bthen)
        (Term.eval srk termalg belse)
  and alg = function
    | `Tru -> mk_true srk
    | `Fls -> mk_false srk
    | `Atom (`Eq, x, y) -> mk_eq 
                             srk 
                             (Term.eval srk termalg x) 
                             (Term.eval srk termalg y)
    | `Atom (`Lt, x, y) -> mk_lt 
                             srk 
                             (Term.eval srk termalg x) 
                             (Term.eval srk termalg y)
    | `Atom (`Leq, x, y) -> mk_leq 
                              srk 
                              (Term.eval srk termalg x) 
                              (Term.eval srk termalg y)
    | `And conjuncts -> mk_and srk conjuncts
    | `Or disjuncts -> mk_or srk disjuncts
    | `Quantify _ ->
      failwith "not matrix"
    | `Not _ -> failwith "not positive"
    | `Proposition (`Var i) -> mk_var srk i `TyBool
    | `Proposition (`App (p, args)) ->
      mk_app 
        srk 
        p 
        (List.map (fun arg -> 
             begin match Expr.refine srk arg with 
               | `Term t -> ((Term.eval srk termalg t) :> ('a, typ_fo) expr)
               | `Formula f -> ((Formula.eval srk alg f) :> ('a, typ_fo) expr)
             end)
            args) 
    | `Ite (cond, bthen, belse) ->
          mk_ite srk cond bthen belse
  in
  let matrix = Formula.eval srk alg matrix in
  let qfp = 
    (BatList.make 
       ((Hashtbl.length preqfmapsyms) + (Hashtbl.length preqfmapvars)) 
       (`Exists ("_", `TyInt)))
    @qfp in
  let matrix = 
    if bbu = false then matrix
    else(
      let clistconsts = Hashtbl.fold 
          (fun (arrsym, const) ind consistencylist ->
             let conjunct =
               begin match Hashtbl.find_opt arrunivenum arrsym with
                 | None -> mk_true srk
                 | Some debruin ->
                   mk_if 
                     srk 
                     (mk_eq srk 
                        (mk_var srk arrunivcard `TyInt) 
                        (mk_const srk const))
                     (mk_eq 
                        srk 
                        (mk_var srk debruin `TyInt)
                        (mk_var srk ind `TyInt))
               end
             in
             conjunct :: consistencylist)
          preqfmapsyms
          []
      in
      let clistvars = Hashtbl.fold 
          (fun (arrsym, sym) ind consistencylist ->
             let conjunct = 
               begin match Hashtbl.find_opt arrunivenum arrsym with
                 | None -> mk_true srk
                 | Some debruin ->
                   mk_if 
                     srk 
                     (mk_eq srk 
                        (mk_var srk arrunivcard `TyInt) 
                        (mk_var srk sym `TyInt))
                     (mk_eq 
                        srk 
                        (mk_var srk debruin `TyInt)
                        (mk_var srk ind `TyInt))
               end
             in
             conjunct :: consistencylist)
          preqfmapvars
          []
      in
      mk_and srk ([matrix]@clistconsts@clistvars) 
    )
  in
  add_prefix srk (qfp, matrix)

(*let projection = failwith "todo 1"*)

let get_array_syms srk matrix bbu =
  let combine set_pairs = 
    List.fold_left 
      (fun (arrsymuniv, arrsymother) (arrsymuniv0, arrsymother0) ->
         Symbol.Set.union arrsymuniv arrsymuniv0,
         Symbol.Set.union arrsymother arrsymother0)
      (Symbol.Set.empty, Symbol.Set.empty)
      set_pairs

  in
  let rec termalg = function
    | `Real _ | `Var _ -> Symbol.Set.empty, Symbol.Set.empty
    | `App (arrsym, [indvar]) -> 
        begin match destruct srk indvar with
          | `Var (ind, `TyInt) ->
            if bbu && ind = 0 then
              Symbol.Set.add arrsym Symbol.Set.empty,
              Symbol.Set.empty
            else
              Symbol.Set.empty,
              Symbol.Set.add arrsym Symbol.Set.empty
          | `App (_, []) -> 
            Symbol.Set.empty,
            Symbol.Set.add arrsym Symbol.Set.empty
          | _ -> failwith "not flat"
        end
    | `App (_, args) -> 
      combine  
        (List.map (fun arg -> 
             begin match Expr.refine srk arg with 
               | `Term t -> Term.eval srk termalg t
               | `Formula f -> Formula.eval srk alg f
             end)
            args)
    | `Add sum -> combine sum
    | `Mul product -> combine product
    | `Binop (_, s, t) -> combine [s; t]
    | `Unop (_, t) -> t
    | `Ite (cond, bthen, belse) -> combine [Formula.eval srk alg cond;
                                         bthen; belse]
  and  alg = function
    | `Tru | `Fls -> Symbol.Set.empty, Symbol.Set.empty
    | `Atom (_, x, y) -> 
      let arrsymuniv1, arrsymother1 = Term.eval srk termalg x in
      let arrsymuniv2, arrsymother2 = Term.eval srk termalg y in
      Symbol.Set.union arrsymuniv1 arrsymuniv2,
      Symbol.Set.union arrsymother1 arrsymother2
    | `And juncts 
    | `Or juncts ->
      combine juncts
    | `Quantify _ -> failwith "not matrix"
    | `Not _ -> failwith "not positive"
    | `Proposition (`Var _) -> Symbol.Set.empty, Symbol.Set.empty
    | `Proposition (`App (_, args)) -> 
      combine  
        (List.map (fun arg -> 
          begin match Expr.refine srk arg with 
            | `Term t -> Term.eval srk termalg t
            | `Formula f -> Formula.eval srk alg f
          end)
          args)
    | `Ite (cond, bthen, belse) -> combine [cond; bthen; belse]
  in
  Formula.eval srk alg matrix 

(*TODO: figure out a way to unify these*)
let mkb label =
  match label with
  | `Div -> mk_div
  | `Mod -> mk_mod
let mku label =
  match label with
  | `Floor -> mk_floor
  | `Neg -> mk_neg
let mka label =
  match label with
  | `Eq -> mk_eq
  | `Leq -> mk_leq 
  | `Lt -> mk_lt

let new_to_mfa srk phi =
  let open Hashtbl in
  let sb_tbl = create 10 in
  let univequivclass = ref None in
  let basecase_emp = (0, create 0) in
  let basecase_var ind sym =
    add sb_tbl sym (BatUref.uref sym);
    let tbl = create 1 in
    add tbl ind sym;
    (0, tbl)
  in
  let merge offset_tbls =
    let merge_two (off0, tbl0) (off, tbl) =
      let frm_off, frm_tbl, to_off, to_tbl =
        if length tbl0 > length tbl then off, tbl, off0, tbl0
        else off0, tbl0, off, tbl
      in
      let unify frm_ind frm_sym =
        match find_opt to_tbl (to_off + frm_ind - frm_off) with 
        | Some to_sym -> BatUref.unite (find sb_tbl to_sym) (find sb_tbl frm_sym)
        | None -> add to_tbl (to_off + frm_ind - frm_off) frm_sym 
      in
      iter unify frm_tbl;
      to_off, to_tbl
    in
    List.fold_left merge_two basecase_emp offset_tbls
  in
  let rec termalg = function
    | `Real qq -> (basecase_emp, mk_real srk qq)
    | `App (arrsym, [r_term]) -> 
      begin match destruct srk r_term with
        | `Var (ind, `TyInt) ->
          let fresh = mk_symbol srk `TyInt in
          (basecase_var ind fresh, mk_app srk arrsym [mk_const srk fresh])
        | `App (sym, []) -> (basecase_emp, mk_app srk arrsym [mk_const srk sym])
        | _ -> failwith "not in logical fragment"
      end
    | `Var (ind, `TyInt) -> 
      let fresh = mk_symbol srk `TyInt in
      (basecase_var ind fresh, mk_const srk fresh)
    | `Add sum -> 
      let tbls, terms = List.split sum in
      merge tbls, mk_add srk terms
    | `Mul product -> 
      let tbls, terms = List.split product in
      merge tbls, mk_mul srk terms
    | `Binop (lbl, (tbl1, term1), (tbl2, term2)) -> 
      merge [tbl1; tbl2], (mkb lbl) srk term1 term2
    | `Unop (lbl, (tbl, t)) -> tbl, (mku lbl) srk t
    | `Ite (_, _, _) -> 
      (*mk_ite 
        srk 
        (Formula.eval srk alg cond)
        (Term.eval srk termalg  bthen)
        (Term.eval srk termalg belse)*) failwith "todo"
    |  _ -> failwith "not in pmfa fragment"
 and alg = function
    | `Tru -> basecase_emp, mk_true srk
    | `Fls -> basecase_emp, mk_false srk
    | `Atom (lbl, x, y) ->
      let tbl1, term1 = Term.eval srk termalg x in
      let tbl2, term2 = Term.eval srk termalg y in
      merge [tbl1; tbl2], (mka lbl) srk term1 term2
    | `And cons ->
      let tbls, terms = List.split cons in
      merge tbls, mk_and srk terms
    | `Or disj -> 
      let tbls, terms = List.split disj in
      merge tbls, mk_or srk terms
    | `Quantify (`Exists, _, `TyInt, ((offset, tbl), phi)) ->
      remove tbl offset;
      (offset+1, tbl), phi
    | `Quantify (`Forall, _, `TyInt, ((offset, tbl), phi)) ->
       if !univequivclass = None && mem tbl offset then
         univequivclass := Some (find sb_tbl (find tbl offset))
       else ();
       remove tbl offset;
       (offset+1, tbl), phi
    | _ -> failwith "not in pmfa logical fragment"
  in
  let ((_, _), matr) = Formula.eval srk alg phi in
  let matr = 
    substitute_const 
      srk
      (fun sym -> 
         match find_opt sb_tbl sym with
         | Some uref -> 
           if Option.is_none !univequivclass || 
              not (BatUref.equal (Option.get !univequivclass) uref)
           then 
             mk_const srk (BatUref.uget uref)
           else mk_var srk 0 `TyInt
         | None -> mk_const srk sym)
    matr
  in
  mk_forall srk `TyInt matr


module Array_analysis (Iter : PreDomain) = struct

  type 'a t = 'a formula

  let abstract = failwith "todo 4"

  let equal = failwith "todo 5"

  let widen = failwith "todo 6"

  let join = failwith "todo 7"

  let exp srk _ _ phi =
    let qpf, bbu, matr = to_mfa srk phi in
    let arruniv, arrother = get_array_syms srk matr bbu in
    let lia = mfa_to_lia srk (qpf, matr) arruniv arrother bbu in 
    lia

  let pp = failwith "todo 10"

end
