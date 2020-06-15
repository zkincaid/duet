open Syntax
module V = Linear.QQVector
module M = Linear.QQMatrix
module Z = Linear.ZZVector
module H = Abstract
include Log.Make(struct let name = "srk.array:" end)

type 'a t = 'a formula

type qfp =  [ `Exists of string * Syntax.typ_fo
            | `Forall of string * Syntax.typ_fo ] list

let to_mfa srk phi =
  let combine phis =
    let f (qf_pre0, boundbyuniv0, phi0) (eqf_pre, boundbyuniv, phis) =
      if boundbyuniv0 = true && boundbyuniv = true
      then (
        let eqf_pre0 = List.tl (List.rev qf_pre0) in
        let depth = List.length eqf_pre  in 
        let depth0 = List.length eqf_pre0 in (*not counting univ quant*)
        let phis = List.map (decapture srk (depth + 1) depth0) phis in
        (eqf_pre0@eqf_pre, boundbyuniv0 || boundbyuniv, 
         (decapture srk 1 depth phi0)::phis)
      )
      else if boundbyuniv0 = true && boundbyuniv = false
      then (
        let eqf_pre0 = List.tl (List.rev qf_pre0) in
        let depth = List.length eqf_pre  in 
        let depth0 = List.length eqf_pre0 in (*not counting univ quant*)
        let phis = List.map (decapture srk 0 1) phis in
        let phis = List.map (decapture srk (depth + 1) depth0) phis in
        (eqf_pre0@eqf_pre, boundbyuniv0 || boundbyuniv, 
         (decapture srk 1 depth phi0)::phis)
      )
      else if boundbyuniv0 = false && boundbyuniv = true
      then (
        let eqf_pre0 = qf_pre0 in
        let depth = List.length eqf_pre  in 
        let depth0 = List.length eqf_pre0 in (*not counting univ quant*)
        let phis = List.map (decapture srk (depth + 1) depth0) phis in
        (eqf_pre0@eqf_pre, boundbyuniv0 || boundbyuniv, 
         (decapture srk 0 (depth + 1) phi0)::phis)
      )
      else
        (
          let eqf_pre0 = qf_pre0 in
          let depth = List.length eqf_pre  in 
          let depth0 = List.length eqf_pre0 in (*not counting univ quant*)
          let phis = List.map (decapture srk depth depth0) phis in
          (eqf_pre0@eqf_pre, boundbyuniv0 || boundbyuniv, 
           (decapture srk 0 depth phi0)::phis)
        )
    in
    List.fold_right f phis ([], false, [])
  in
  let alg = function
    | `Tru -> ([], false, mk_true srk)
    | `Fls -> ([], false, mk_false srk)
    | `Atom (`Eq, x, y) -> ([], false, mk_eq srk x y)
    | `Atom (`Lt, x, y) -> ([], false, mk_lt srk x y)
    | `Atom (`Leq, x, y) -> ([], false, mk_leq srk x y)
    | `And conjuncts ->
      let (eqf_pre, bbu, conjuncts) = combine conjuncts in
      if bbu = false then
        (eqf_pre, bbu, mk_and srk conjuncts)
      else 
        (eqf_pre@[`Forall ("_", `TyInt)], bbu, mk_and srk conjuncts)
    | `Or disjuncts ->
      let (eqf_pre, bbu, disjuncts) = combine disjuncts in
      if bbu = false then
        (eqf_pre, bbu, mk_or srk disjuncts)
      else 
        ((`Exists ("_", `TyInt)) :: eqf_pre@[`Forall ("_", `TyInt)], 
         bbu, 
         mk_or 
           srk 
           (List.mapi 
              (fun ind disjunct -> 
                 mk_and 
                   srk 
                   [disjunct; 
                    mk_eq 
                      srk 
                      (mk_int srk ind)  
                      (mk_var srk (List.length eqf_pre + 2) `TyInt)]) 
              disjuncts))
    | `Quantify (`Exists, name, typ, (qf_pre, bbu, phi)) ->
      (`Exists (name, typ)::qf_pre, bbu, phi)
    | `Quantify (`Forall, name, typ, (qf_pre, bbu, phi)) ->
      if bbu then failwith "not monic"
      else (`Forall (name, typ)::qf_pre, true, phi)
    | `Not (_, _, _) -> failwith "not positive"
    | `Proposition (`Var i) -> ([], false, mk_var srk i `TyBool)
    | `Proposition (`App (p, args)) -> ([], false, mk_app srk p args)
    | `Ite (cond, bthen, belse) ->
      begin match combine [cond; bthen; belse] with
        | (qf_pre, bbu, [cond; bthen; belse]) ->
          (qf_pre, bbu, mk_ite srk cond bthen belse)
        | _ -> assert false
      end
  in
  let qf_pre, _, matrix = Formula.eval srk alg phi in
  qf_pre, matrix
(*List.fold_right
  (fun qf phi ->
     match qf with
     | `Exists (name, typ) -> mk_exists srk ~name typ phi
     | `Forall (name, typ) -> mk_forall srk ~name typ phi)
  qf_pre
  matrix
*)

let add_prefix srk (qf_pre, matrix) =
  List.fold_right
    (fun qf phi ->
       match qf with
       | `Exists (name, typ) -> mk_exists srk ~name typ phi
       | `Forall (name, typ) -> mk_forall srk ~name typ phi)
    qf_pre
    matrix

let mfa_to_lia srk (qfp, matrix) arr_preds =
  let enumcounter = ref 0 in
  let numarrs = Symbol.Set.cardinal arr_preds in
  let arrenum = Hashtbl.create numarrs in
  Symbol.Set.iter 
    (fun arrsym -> Hashtbl.add arrenum arrsym !enumcounter; 
      enumcounter := !enumcounter + 1) 
    arr_preds;
  let innerqf = BatList.make numarrs (`Exists ("_", `TyInt)) in
  let qfp = qfp@innerqf in
  let matrix = decapture srk 0 numarrs matrix in
  let qfcounter = ref (List.length qfp) in
  let preqfmapsyms = Hashtbl.create numarrs in
  let preqfmapvars = Hashtbl.create numarrs in
  let termalg = function
    | `Real qq -> mk_real srk qq
    | `App (arrsym, [indvar]) -> 
      if Symbol.Set.mem arrsym arr_preds then
        begin match destruct srk indvar with
        | `Var (ind, `TyInt) ->
          if ind = numarrs then
            mk_var srk (Hashtbl.find arrenum arrsym) `TyInt
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
      else mk_app srk arrsym [indvar]
    | `App (func, args) -> mk_app srk func args
    | `Var (i, `TyInt) -> mk_var srk i `TyInt
    | `Var (i, `TyReal) -> mk_var srk i `TyReal
    | `Add sum -> mk_add srk sum
    | `Mul product -> mk_add srk product
    | `Binop (`Div, s, t) -> mk_div srk s t
    | `Binop (`Mod, s, t) -> mk_mod srk s t
    | `Unop (`Floor, t) -> mk_floor srk t
    | `Unop (`Neg, t) -> mk_neg srk t
    | `Ite (cond, bthen, belse) -> mk_ite srk cond bthen belse
  in
  let te = Term.eval srk termalg in
  let alg = function
    | `Tru -> mk_true srk
    | `Fls -> mk_false srk
    | `Atom (`Eq, x, y) -> mk_eq srk (te x) (te y)
    | `Atom (`Lt, x, y) -> mk_lt srk (te x) (te y)
    | `Atom (`Leq, x, y) -> mk_leq srk (te x) (te y)
    | `And conjuncts -> mk_and srk conjuncts
    | `Or disjuncts -> mk_or srk disjuncts
    | `Quantify _ ->
      failwith "not matrix"
    | `Not _ -> failwith "not positive"
    | `Proposition (`Var i) -> mk_var srk i `TyBool
    | `Proposition (`App (p, args)) ->
       mk_app srk p args
    | `Ite (cond, bthen, belse) ->
          mk_ite srk cond bthen belse
  in
  (*let matrix = substitute_sym srk 
      (fun sym -> mk_const srk (mk_symbol srk ~name:"test" `TyInt))
      matrix in*)
  let matrix = Formula.eval srk alg matrix in
  let qfp = 
    (BatList.make 
       ((Hashtbl.length preqfmapsyms) + (Hashtbl.length preqfmapvars)) 
       (`Exists ("_", `TyInt)))
    @qfp in
  let clistconsts = Hashtbl.fold 
      (fun (arrsym, sym) ind consistencylist ->
         let conjunct = 
         mk_if 
           srk 
           (mk_eq srk (mk_var srk numarrs `TyInt) (mk_const srk sym))
           (mk_eq 
              srk 
              (mk_var srk (Hashtbl.find arrenum arrsym) `TyInt)
              (mk_var srk ind `TyInt))
         in
         conjunct :: consistencylist)
      preqfmapsyms
      []
  in
  let clistvars = Hashtbl.fold 
      (fun (arrsym, sym) ind consistencylist ->
         let conjunct = 
           mk_if 
             srk 
             (mk_eq srk (mk_var srk numarrs `TyInt) (mk_var srk sym `TyInt))
             (mk_eq 
                srk 
                (mk_var srk (Hashtbl.find arrenum arrsym) `TyInt)
                (mk_var srk ind `TyInt))
         in
         conjunct :: consistencylist)
      preqfmapvars
      []
  in
  let matrix = mk_and srk ([matrix]@clistconsts@clistvars) in
  add_prefix srk (qfp, matrix)
