open Syntax
open BatPervasives

module V = Linear.QQVector
module Monomial = Polynomial.Monomial
module P = Polynomial.Mvp
module Rewrite = Polynomial.Rewrite
module IntSet = SrkUtil.Int.Set

include Log.Make(struct let name = "srk.coordinateSystem" end)

type cs_term = [ `Mul of V.t * V.t
               | `Inv of V.t
               | `Mod of V.t * V.t
               | `Floor of V.t
               | `App of symbol * (V.t list) ]

(* Env needs to map a set of synthetic terms into an initial segment of the
   naturals, with all of the integer-typed synthetic terms mapped to smaller
   naturals than real-typed synthetic termsg *)
module A = BatDynArray

type 'a t =
  { srk : 'a context;
    term_id : (cs_term, int) Hashtbl.t;
    id_def : (cs_term * int * [`TyInt | `TyReal]) A.t }

let const_id = -1

let dim cs = A.length cs.id_def
let int_dim cs =
  let ints = ref 0 in
  cs.id_def |> A.iter (function
      | (_, _, `TyInt) -> incr ints
      | (_, _, `TyReal) -> ());
  !ints
let real_dim cs = (dim cs) - (int_dim cs)
  
  
let mk_empty srk =
  { srk = srk;
    term_id = Hashtbl.create 991;
    id_def = A.create () }

let get_context cs = cs.srk

let copy cs =
  { srk = cs.srk;
    term_id = Hashtbl.copy cs.term_id;
    id_def = A.copy cs.id_def }

let destruct_coordinate cs id =
  let (term, _, _) = A.get cs.id_def id in
  term

let rec term_of_coordinate cs id =
  match destruct_coordinate cs id with
  | `Mul (x, y) -> mk_mul cs.srk [term_of_vec cs x; term_of_vec cs y]
  | `Inv x -> mk_div cs.srk (mk_real cs.srk QQ.one) (term_of_vec cs x)
  | `Mod (x, y) -> mk_mod cs.srk (term_of_vec cs x) (term_of_vec cs y)
  | `Floor x -> mk_floor cs.srk (term_of_vec cs x)
  | `App (func, args) -> mk_app cs.srk func (List.map (term_of_vec cs) args)

and term_of_vec cs vec =
  (V.enum vec)
  /@ (fun (coeff, id) ->
      if id = const_id then
        mk_real cs.srk coeff
      else if QQ.equal QQ.one coeff then
        term_of_coordinate cs id
      else
        mk_mul cs.srk [mk_real cs.srk coeff; term_of_coordinate cs id])
  |> BatList.of_enum
  |> mk_add cs.srk

let level_of_id cs id =
  let (_, level, _) = A.get cs.id_def id in
  level

let type_of_id cs id =
  let (_, _, typ) = A.get cs.id_def id in
  typ

let level_of_vec cs vec =
  BatEnum.fold
    (fun level (_, id) ->
       if id = const_id then
         level
       else
         max level (level_of_id cs id))
    (-1)
    (V.enum vec)

let type_of_vec cs vec =
  let is_integral (coeff, id) =
    QQ.to_zz coeff != None
    && (id = const_id || type_of_id cs id = `TyInt)
  in
  if BatEnum.for_all is_integral (V.enum vec) then
    `TyInt
  else
    `TyReal

let join_typ s t = match s,t with
  | `TyInt, `TyInt -> `TyInt
  | _, _ -> `TyReal

let srk cs = cs.srk

let pp formatter cs =
  Format.fprintf formatter "[@[<v 0>";
  cs.id_def |> A.iteri (fun id _ ->
      Format.fprintf formatter "%d -> %a (%s)@;"
        id
        (Term.pp cs.srk) (term_of_coordinate cs id)
        (match type_of_id cs id with | `TyInt -> "int" | `TyReal -> "real"));
  Format.fprintf formatter "@]]"

let rec pp_vector cs formatter vec =
  let pp_elt formatter (k, id) =
    if id = const_id then
      QQ.pp formatter k
    else if QQ.equal k QQ.one then
      pp_cs_term cs formatter (destruct_coordinate cs id)
    else
      Format.fprintf formatter "%a@ * (@[%a@])"
        QQ.pp k
        (pp_cs_term cs) (destruct_coordinate cs id)
  in
  let pp_sep formatter () = Format.fprintf formatter " +@ " in
  if V.is_zero vec then
    Format.pp_print_string formatter "0"
  else
    Format.fprintf formatter "@[<hov 1>%a@]"
      (SrkUtil.pp_print_enum ~pp_sep pp_elt) (V.enum vec)

and pp_cs_term cs formatter = function
  | `Mul (x, y) ->
    Format.fprintf formatter "@[<hov 1>(%a)@ * (%a)@]"
      (pp_vector cs) x
      (pp_vector cs) y
  | `Inv x ->
    Format.fprintf formatter "1/(@[<hov 1>%a@])"
      (pp_vector cs) x
  | `Mod (x, y) ->
    Format.fprintf formatter "@[<hov 1>(%a)@ mod (%a)@]"
      (pp_vector cs) x
      (pp_vector cs) y
  | `Floor x ->
    Format.fprintf formatter "floor(@[%a@])"
      (pp_vector cs) x
  | `App (const, []) ->
    Format.fprintf formatter "%a" (pp_symbol cs.srk) const
  | `App (func, args) ->
    let pp_comma formatter () = Format.fprintf formatter ",@ " in
    Format.fprintf formatter "%a(@[<hov 1>%a@])"
      (pp_symbol cs.srk) func
      (SrkUtil.pp_print_enum ~pp_sep:pp_comma (pp_vector cs))
      (BatList.enum args)

let cs_term_id ?(admit=false) cs t =
  if Hashtbl.mem cs.term_id t then
    Hashtbl.find cs.term_id t
  else if admit then
    let id = A.length cs.id_def in
    let (typ, level) = match t with
      | `Mul (s, t) | `Mod (s, t) ->
        (join_typ (type_of_vec cs s) (type_of_vec cs t),
         max (level_of_vec cs s) (level_of_vec cs t))
      | `Floor x ->
        (`TyInt, level_of_vec cs x)
      | `Inv x ->
        (`TyReal, level_of_vec cs x)
      | `App (func, args) ->
        let typ =
          match typ_symbol cs.srk func with
          | `TyFun (_, `TyInt) | `TyInt -> `TyInt
          | `TyFun (_, `TyReal) | `TyReal -> `TyReal
          | `TyFun (_, `TyBool) | `TyBool -> `TyInt
        in
        let level =
          List.fold_left max 0 (List.map (level_of_vec cs) args)
        in
        (typ, level)
    in
    A.add cs.id_def (t, level, typ);
    Hashtbl.add cs.term_id t id;
    logf ~level:`trace "Admitted %s: %d -> %a"
      (match typ with `TyInt -> "int" | `TyReal -> "real")
      id
      (pp_cs_term cs) t;
    id
  else
    raise Not_found

let const_of_vec vec =
  let (const_coeff, rest) = V.pivot const_id vec in
  if V.is_zero rest then
    Some const_coeff
  else
    None

let vec_of_term ?(admit=false) cs =
  let rec alg = function
    | `Real k -> V.of_term k const_id
    | `App (symbol, []) ->
      V.of_term QQ.one (cs_term_id ~admit cs (`App (symbol, [])))

    | `App (symbol, xs) ->
      let xs =
        List.map (fun x ->
            match Expr.refine cs.srk x with
            | `Term t -> Term.eval cs.srk alg t
            | `Formula _ -> assert false) (* TODO *)
          xs
      in
      V.of_term QQ.one (cs_term_id ~admit cs (`App (symbol, xs)))

    | `Var (_, _) -> assert false (* to do *)
    | `Add xs -> List.fold_left V.add V.zero xs
    | `Mul xs ->
      (* Factor out scalar multiplication *)
      let (k, xs) =
        List.fold_right (fun y (k,xs) ->
            match const_of_vec y with
            | Some k' -> (QQ.mul k k', xs)
            | None -> (k, y::xs))
          xs
          (QQ.one, [])
      in
      begin match xs with
        | [] -> V.of_term k const_id
        | x::xs ->
          let mul x y =
            V.of_term QQ.one (cs_term_id ~admit cs (`Mul (x, y)))
          in
          V.scalar_mul k (List.fold_left mul x xs)
      end
    | `Binop (`Div, x, y) ->
      let denomenator = V.of_term QQ.one (cs_term_id ~admit cs (`Inv y)) in
      let (k, xrest) = V.pivot const_id x in
      if V.equal xrest V.zero then
        V.scalar_mul k denomenator
      else
        V.of_term QQ.one (cs_term_id ~admit cs (`Mul (x, denomenator)))
    | `Binop (`Mod, x, y) ->
      V.of_term QQ.one (cs_term_id ~admit cs (`Mod (x, y)))
    | `Unop (`Floor, x) ->
      V.of_term QQ.one (cs_term_id ~admit cs (`Floor x))
    | `Unop (`Neg, x) -> V.negate x
    | `Ite (_, _, _) -> assert false (* No ites in implicants *)
  in
  Term.eval cs.srk alg

let admits cs t =
  try
    ignore (vec_of_term ~admit:false cs t);
    true
  with Not_found -> false

let rec polynomial_of_coordinate cs id =
  match destruct_coordinate cs id with
  | `Mul (x, y) -> P.mul (polynomial_of_vec cs x) (polynomial_of_vec cs y)
  | _ -> P.of_dim id
and polynomial_of_vec cs vec =
  let (const_coeff, vec) = V.pivot const_id vec in
  V.enum vec
  /@ (fun (coeff, id) -> P.scalar_mul coeff (polynomial_of_coordinate cs id))
  |> BatEnum.fold P.add (P.scalar const_coeff)

let polynomial_of_term cs term =
  polynomial_of_vec cs (vec_of_term cs term)

let term_of_polynomial cs = P.term_of cs.srk (term_of_coordinate cs)

let admit_term cs term = ignore (vec_of_term ~admit:true cs term)
let admit_cs_term cs term = ignore (cs_term_id ~admit:true cs term)

exception Unsafe
let project_ideal cs ideal ?(subterm=fun x -> true) keep =
  let dimension = dim cs in
  let srk = cs.srk in
  let subterm x = subterm x && keep x in
  let safe_term = Array.make dimension None in
  let integrity = Array.make dimension (mk_true srk) in
  for i = 0 to dimension - 1 do
    let term = term_of_coordinate cs i in
    if Symbol.Set.for_all subterm (symbols term) then
      safe_term.(i) <- Some term
  done;
  let is_unsafe k = safe_term.(k) = None in
  let order =
    Monomial.block [is_unsafe] Monomial.degrevlex
  in
  let safe_term_of_coordinate k =
    match safe_term.(k) with
    | None -> raise Unsafe
    | Some t -> t
  in
  let continue = ref true in
  while !continue do
    continue := false;
    let rewrite =
      Rewrite.mk_rewrite order ideal
      |> Rewrite.grobner_basis
    in
    let safe_term_of_polynomial p =
      let (p, provenance) = Rewrite.preduce rewrite p in
      let term = P.term_of srk safe_term_of_coordinate p in
      let safe_term_constraints =
        P.dimensions p
        /@ (fun i ->
            let term = term_of_coordinate cs i in
            let term' = safe_term_of_coordinate i in
            mk_eq srk term term')
        |> BatList.of_enum
      in
      let provenance_constraints =
        List.map (fun q ->
            mk_eq srk (term_of_polynomial cs q) (mk_real srk QQ.zero))
          provenance
      in
      (term, mk_and srk (provenance_constraints@safe_term_constraints))
    in
    let safe_term_of_vec vec =
      safe_term_of_polynomial (polynomial_of_vec cs vec)
    in
    for i = 0 to dimension - 1 do
      if safe_term.(i) = None then begin
        try
          let (safe, hypothesis) =
            match destruct_coordinate cs i with
            | `Inv x ->
              let (x', integrity) = safe_term_of_vec x in
              (mk_div srk (mk_real srk QQ.one) x', integrity)
            | `Mul (x, y) ->
              let (x', xintegrity) = safe_term_of_vec x in
              let (y', yintegrity) = safe_term_of_vec y in
              (mk_mul srk [x'; y'], mk_and srk [xintegrity; yintegrity])
              (* safe_term_of_polynomial (polynomial_of_coordinate cs i) *)
            | `Mod (x, y) ->
              let (x', xintegrity) = safe_term_of_vec x in
              let (y', yintegrity) = safe_term_of_vec y in
              (mk_mod srk x' y', mk_and srk [xintegrity; yintegrity])
            | `Floor x ->
              let (x', integrity) = safe_term_of_vec x in
              (mk_floor srk x', integrity)
            | `App (_, []) -> raise Unsafe
            | `App (func, args) when keep func ->
              let safe = List.map safe_term_of_vec args in
              let args' = List.map fst safe in
              let integrity = List.map snd safe in
              (mk_app srk func args', mk_and srk integrity)
            | `App (_, _) -> raise Unsafe
          in
          let conclusion = mk_eq srk safe (term_of_coordinate cs i) in
          logf ~level:`trace "Safe: %a -> %a" (Term.pp srk) (term_of_coordinate cs i)
            (Term.pp srk) safe;
          safe_term.(i) <- Some safe;
          integrity.(i) <- mk_if srk hypothesis conclusion;
          continue := true
        with Unsafe -> ()
      end
    done
  done;
  for i = 0 to dimension - 1 do
    match destruct_coordinate cs i with
    | `App (sym, []) ->
      if keep sym then
        safe_term.(i) <- Some (mk_const srk sym)
    | _ -> ()
  done;
  BatEnum.fold (fun safe i ->
      let id = dimension - i in
      match safe_term.(id) with
      | Some t -> (id, t, integrity.(id))::safe
      | None -> safe)
    []
    (1 -- dimension)

let subcoordinates cs i =
  let rec add_vec_coordinates set v =
    BatEnum.fold
      (fun set (_, coord) -> add_subcoordinates set coord)
      set
      (V.enum v)
  and add_subcoordinates set coord =
    if IntSet.mem coord set then
      set
    else match destruct_coordinate cs coord with
      | `App (_, args) ->
        List.fold_left add_vec_coordinates IntSet.empty args
      | `Mul (x, y) | `Mod (x, y) ->
        add_vec_coordinates (add_vec_coordinates set x) y
      | `Inv x | `Floor x ->
        add_vec_coordinates set x
  in
  add_subcoordinates IntSet.empty i
  |> IntSet.remove const_id

let direct_subcoordinates cs i =
  let add_vec_coordinates set v =
    BatEnum.fold
      (fun set (_, coord) -> IntSet.add coord set)
      set
      (V.enum v)
  in
  let subcoordinates =
    match destruct_coordinate cs i with
    | `App (_, args) ->
      List.fold_left add_vec_coordinates IntSet.empty args
    | `Mul (x, y) | `Mod (x, y) ->
      add_vec_coordinates (add_vec_coordinates IntSet.empty x) y
    | `Inv x | `Floor x ->
      add_vec_coordinates IntSet.empty x
  in
  IntSet.remove const_id subcoordinates
