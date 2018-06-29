open Syntax
open BatPervasives

include Log.Make(struct let name = "srk.iteration" end)

module V = Linear.QQVector
module QQMatrix = Linear.QQMatrix

module IntSet = SrkUtil.Int.Set
module IntMap = SrkUtil.Int.Map
module DArray = BatDynArray

module QQX = Polynomial.QQX
module QQXs = Polynomial.QQXs
module Monomial = Polynomial.Monomial
module MonomialSet = Set.Make(Monomial)
module CS = CoordinateSystem

module UP = ExpPolynomial.UltPeriodic
module UPXs = struct
  include Polynomial.MakeMultivariate(UP)

  let eval upxs k =
    BatEnum.fold (fun e (up, m) ->
        QQXs.add_term (UP.eval up k) m e)
      QQXs.zero
      (enum upxs)

  let map_coeff f upxs =
    BatEnum.fold (fun e (up, m) ->
        add_term (f m up) m e)
      zero
      (enum upxs)

  let flatten period =
    let monomials =
      List.fold_left (fun set upxs ->
          BatEnum.fold (fun set (_, m) ->
              MonomialSet.add m set)
            set
            (enum upxs))
        MonomialSet.empty
        period
    in
    MonomialSet.fold (fun m upxs ->
        let up =
          List.map (coeff m) period
          |> UP.flatten
        in
        add_term up m upxs)
      monomials
      zero
end

module type PreDomain = sig
  type 'a t
  val pp : 'a context -> (symbol * symbol) list -> Format.formatter -> 'a t -> unit
  val exp : 'a context -> (symbol * symbol) list -> 'a term -> 'a t -> 'a formula
  val join : 'a context -> (symbol * symbol) list -> 'a t -> 'a t -> 'a t
  val widen : 'a context -> (symbol * symbol) list -> 'a t -> 'a t -> 'a t
  val equal : 'a context -> (symbol * symbol) list -> 'a t -> 'a t -> bool
  val abstract : ?exists:(symbol -> bool) ->
    'a context ->
    (symbol * symbol) list ->
    'a formula ->
    'a t
end

module type PreDomainWedge = sig
  include PreDomain
  val abstract_wedge : 'a context -> (symbol * symbol) list -> 'a Wedge.t -> 'a t
end

module type Domain = sig
  type 'a t
  val pp : Format.formatter -> 'a t -> unit
  val closure : 'a t -> 'a formula
  val join : 'a t -> 'a t -> 'a t
  val widen : 'a t -> 'a t -> 'a t
  val equal : 'a t -> 'a t -> bool
  val abstract : ?exists:(symbol -> bool) ->
    'a context ->
    (symbol * symbol) list ->
    'a formula ->
    'a t
  val tr_symbols : 'a t -> (symbol * symbol) list
end

let identity srk tr_symbols =
  List.map (fun (sym, sym') ->
      mk_eq srk (mk_const srk sym) (mk_const srk sym'))
    tr_symbols
  |> mk_and srk

let pre_symbols tr_symbols =
  List.fold_left (fun set (s,_) ->
      Symbol.Set.add s set)
    Symbol.Set.empty
    tr_symbols

let post_symbols tr_symbols =
  List.fold_left (fun set (_,s') ->
      Symbol.Set.add s' set)
    Symbol.Set.empty
    tr_symbols

(* Map from pre-state vars to their post-state counterparts *)
let post_map tr_symbols =
  List.fold_left
    (fun map (sym, sym') -> Symbol.Map.add sym sym' map)
    Symbol.Map.empty
    tr_symbols

let term_of_ocrs srk loop_counter pre_term_of_id post_term_of_id =
  let open Ocrs in
  let open Type_def in
  let ss_pre = SSVar "k" in
  let rec go = function
    | Plus (x, y) -> mk_add srk [go x; go y]
    | Minus (x, y) -> mk_sub srk (go x) (go y)
    | Times (x, y) -> mk_mul srk [go x; go y]
    | Divide (x, y) -> mk_div srk (go x) (go y)
    | Product xs -> mk_mul srk (List.map go xs)
    | Sum xs -> mk_add srk (List.map go xs)
    | Symbolic_Constant name -> pre_term_of_id name
    | Base_case (name, index) ->
      assert (index = 0);
      pre_term_of_id name
    | Input_variable name ->
      assert (name = "k");
      loop_counter
    | Output_variable (name, subscript) ->
      assert (subscript = ss_pre);
      post_term_of_id name
    | Rational k -> mk_real srk (Mpqf.of_mpq k)
    | Undefined -> assert false
    | Pow (x, y) -> Nonlinear.mk_pow srk (go x) (go y)
    | Log (base, x) ->
      Nonlinear.mk_log srk (mk_real srk (Mpqf.of_mpq base)) (go x)
    | IDivide (x, y) ->
      mk_idiv srk (go x) (mk_real srk (Mpqf.of_mpq y))
    | Mod (x, y) ->
      mk_mod srk (go x) (go y)
    | Iif (func, ss) ->
      let arg =
        match ss with
        | SSVar "k" -> loop_counter
        | SAdd ("k", i) ->
          mk_add srk [loop_counter; mk_real srk (QQ.of_int i)]
        | _ -> assert false
      in
      let sym =
        if not (is_registered_name srk func) then
          register_named_symbol srk func (`TyFun ([`TyReal], `TyReal));
        get_named_symbol srk func
      in
      mk_app srk sym [arg]
    | Binomial (_, _) | Factorial _ | Sin _ | Cos _ | Arctan _ | Pi | Shift (_, _) ->
      assert false
  in
  go

exception IllFormedRecurrence

(* Are most coefficients of a vector negative? *)
let is_vector_negative vec =
  let sign =
    BatEnum.fold (fun sign (coeff,_) ->
        if QQ.lt coeff QQ.zero then
          sign - 1
        else
          sign + 1)
      0
      (V.enum vec)
  in
  sign < 0

(* Matrix-polynomial vector multiplication.  Assumes that the columns of m are
   a subset of {0,...,|polyvec|-1}. *)
let matrix_polyvec_mul m polyvec =
  Array.init (QQMatrix.nb_rows m) (fun i ->
      BatEnum.fold (fun p (coeff, j) ->
          QQXs.add p (QQXs.scalar_mul coeff polyvec.(j)))
        QQXs.zero
        (V.enum (QQMatrix.row i m)))

let polyvec_add polyvec polyvec' =
  Array.init (Array.length polyvec) (fun i ->
      QQXs.add polyvec.(i) polyvec'.(i))

let vec_upxsvec_dot vec1 vec2 =
  BatEnum.fold (fun ep i ->
      UPXs.add
        ep
        (UPXs.scalar_mul (UP.scalar (V.coeff i vec1)) vec2.(i)))
    UPXs.zero
    (0 -- (Array.length vec2 - 1))

let vec_qqxsvec_dot vec1 vec2 =
  BatEnum.fold (fun ep i ->
      QQXs.add
        ep
        (QQXs.scalar_mul (V.coeff i vec1) vec2.(i)))
    QQXs.zero
    (0 -- (Array.length vec2 - 1))


(* Write the affine hull of a wedge as Ax' = Bx + c, where c is vector of
   polynomials in recurrence terms, and the non-zero rows of A are linearly
   independent. *)
let rec_affine_hull srk wedge tr_symbols rec_terms rec_ideal =
  let cs = Wedge.coordinate_system wedge in

  (* pre_dims is a set of dimensions corresponding to pre-state
     dimensions. pre_map is a mapping from dimensions that correspond to
     post-state dimensions to their pre-state counterparts *)
  let (pre_map, pre_dims) =
    List.fold_left (fun (pre_map, pre_dims) (s,s') ->
        let id_of_sym sym =
          try
            CS.cs_term_id cs (`App (sym, []))
          with Not_found ->
            assert false
        in
        let pre = id_of_sym s in
        let post = id_of_sym s' in
        (IntMap.add post pre pre_map, IntSet.add pre pre_dims))
      (IntMap.empty, IntSet.empty)
      tr_symbols
  in

  (* An additive dimension is one that is allowed to appear as an additive
     term *)
  let cs_dim = CS.dim cs in
  let additive_dim x = x >= cs_dim in
  let post_dim x = IntMap.mem x pre_map in
  let pp_coord formatter i =
    if i < cs_dim then
      Format.fprintf formatter "w[%a]"
        (Term.pp srk) (CS.term_of_coordinate cs i)
    else
      Format.fprintf formatter "v[%a]"
        (Term.pp srk) (DArray.get rec_terms (i - cs_dim))
  in
  let rec_term_rewrite =
    let ideal = ref rec_ideal in
    let elim_order =
      Monomial.block [not % additive_dim] Monomial.degrevlex
    in
    rec_terms |> DArray.iteri (fun i t ->
        let vec = CS.vec_of_term cs t in
        let p =
          QQXs.add_term
            (QQ.of_int (-1))
            (Monomial.singleton (i + cs_dim) 1)
            (QQXs.of_vec ~const:(CS.const_id) vec)
        in
        ideal := p::(!ideal));
    Polynomial.Rewrite.mk_rewrite elim_order (!ideal)
    |> Polynomial.Rewrite.grobner_basis
  in
  let basis =
    let elim_order =
      Monomial.block [not % additive_dim; not % post_dim] Monomial.degrevlex
    in
    BatList.filter_map
      (fun x ->
         let x' = Polynomial.Rewrite.reduce rec_term_rewrite x in
         if QQXs.equal x' QQXs.zero then
           None
         else
           Some x')
      (Wedge.vanishing_ideal wedge)
    |> Polynomial.Rewrite.mk_rewrite elim_order
    |> Polynomial.Rewrite.grobner_basis
    |> Polynomial.Rewrite.generators
  in
  let (mA, mB, pvc, _) =
    logf ~attributes:[`Bold] "Vanishing ideal:";
    List.fold_left (fun (mA,mB,pvc,i) p ->
        try
          logf "  @[%a@]" (QQXs.pp pp_coord) p;
          let (vecA, vecB, pc) =
            BatEnum.fold (fun (vecA, vecB, pc) (coeff, monomial) ->
                match BatList.of_enum (Monomial.enum monomial) with
                | [(dim, 1)] when IntMap.mem dim pre_map ->
                  (V.add_term (QQ.negate coeff) (IntMap.find dim pre_map) vecA,
                   vecB,
                   pc)
                | [(dim, 1)] when IntSet.mem dim pre_dims ->
                  (vecA, V.add_term coeff dim vecB, pc)
                | monomial_list ->
                  if List.for_all (additive_dim % fst) monomial_list then
                    (vecA, vecB, QQXs.add_term coeff monomial pc)
                  else
                    raise IllFormedRecurrence)
              (V.zero, V.zero, QQXs.zero)
              (QQXs.enum p)
          in
          let (vecA, vecB, pc) =
            if is_vector_negative vecA then
              (V.negate vecA, V.negate vecB, QQXs.negate pc)
            else
              (vecA, vecB, pc)
          in
          let pc =
            QQXs.substitute (fun i ->
                QQXs.add_term
                  QQ.one
                  (Monomial.singleton (i - cs_dim) 1)
                  QQXs.zero)
              pc
          in
          let mAt = QQMatrix.transpose mA in
          match Linear.solve mAt vecA with
          | Some r ->
            (* vecA is already in the span of mA -- r*mA = vecA. *)
            let vecB = V.sub vecB (Linear.vector_left_mul r mB) in
            if V.is_zero vecB then
              (mA, mB, pvc, i)
            else
              let pc =
                let rpc = (* r*pvc *)
                  BatEnum.fold (fun p (coeff, i) ->
                      QQXs.add p (QQXs.scalar_mul coeff (List.nth pvc i)))
                    QQXs.zero
                    (V.enum r)
                in
                QQXs.sub pc rpc
              in
              (mA,
               QQMatrix.add_row i vecB mB,
               pc::pvc,
               i+1)
          | None ->
            (QQMatrix.add_row i vecA mA,
             QQMatrix.add_row i vecB mB,
             pc::pvc,
             i+1)
        with IllFormedRecurrence -> (mA, mB, pvc, i))
      (QQMatrix.zero, QQMatrix.zero, [], 0)
      basis
  in
  (mA, mB, List.rev pvc)

(* Given a wedge w, compute A,B,C such that w |= Ax' = BAx + Cy, and such that
   the row space of A is maximal. *)
let extract_affine_transformation srk wedge tr_symbols rec_terms rec_ideal =
  let (mA, mB, pvc) = rec_affine_hull srk wedge tr_symbols rec_terms rec_ideal in
  let (mT, mB) = Linear.max_lds mA mB in
  let mA = QQMatrix.mul mT mA in
  let pvc = matrix_polyvec_mul mT (Array.of_list pvc) in

  logf ~attributes:[`Blue] "Affine transformation:";
  logf " A: @[%a@]" QQMatrix.pp mA;
  logf " B: @[%a@]" QQMatrix.pp mB;
  (mA, mB, pvc)

module WedgeGuard = struct
  type 'a t =
    { precondition : 'a Wedge.t;
      postcondition : 'a Wedge.t }

  let pp _ _ formatter iter =
    Format.fprintf formatter "pre:@;  @[<v 0>%a@]@;post:@;  @[<v 0>%a@]"
      Wedge.pp iter.precondition
      Wedge.pp iter.postcondition

  let abstract_wedge srk tr_symbols wedge =
    let pre_symbols = pre_symbols tr_symbols in
    let post_symbols = post_symbols tr_symbols in
    let precondition =
      Wedge.exists (not % flip Symbol.Set.mem post_symbols) wedge
    in
    let postcondition =
      Wedge.exists (not % flip Symbol.Set.mem pre_symbols) wedge
    in
    { precondition; postcondition }

  let abstract ?(exists=fun x -> true) srk tr_symbols phi =
    let post_symbols = post_symbols tr_symbols in
    let subterm x = not (Symbol.Set.mem x post_symbols) in
    let wedge =
      Wedge.abstract ~exists ~subterm srk phi
    in
    abstract_wedge srk tr_symbols wedge

  let exp srk tr_symbols loop_counter guard =
    mk_or srk [mk_and srk [mk_eq srk loop_counter (mk_real srk QQ.zero);
                           identity srk tr_symbols];
               mk_and srk [mk_leq srk (mk_real srk QQ.one) loop_counter;
                           Wedge.to_formula guard.precondition;
                           Wedge.to_formula guard.postcondition]]

  let equal _ _ iter iter' =
    Wedge.equal iter.precondition iter'.precondition
    && Wedge.equal iter.postcondition iter'.postcondition

  let join _ _ iter iter' =
    { precondition = Wedge.join iter.precondition iter'.precondition;
      postcondition = Wedge.join iter.postcondition iter'.postcondition }

  let widen _ _ iter iter' =
    { precondition = Wedge.widen iter.precondition iter'.precondition;
      postcondition = Wedge.widen iter.postcondition iter'.postcondition }
end

module LinearRecurrenceInequation = struct
  type 'a t = ('a term * [ `Geq | `Eq ] * QQ.t) list

  let pp srk tr_symbols formatter lr =
    Format.fprintf formatter "@[<v 0>";
    lr |> List.iter (fun (t, op, k) ->
        let opstring = match op with
          | `Geq -> ">="
          | `Eq -> "="
        in
        Format.fprintf formatter "%a %s %a@;" (Term.pp srk) t opstring QQ.pp k);
    Format.fprintf formatter "@]"

  let abstract ?(exists=fun x -> true) srk tr_symbols phi =
    let phi = rewrite srk ~down:(nnf_rewriter srk) phi in
    let delta =
      List.map (fun (s,_) ->
          let name = "delta_" ^ (show_symbol srk s) in
          mk_symbol srk ~name (typ_symbol srk s))
        tr_symbols
    in
    let delta_map =
      List.fold_left2 (fun map delta (s,s') ->
          Symbol.Map.add
            delta
            (mk_sub srk (mk_const srk s') (mk_const srk s))
            map)
        Symbol.Map.empty
        delta
        tr_symbols
    in
    let delta_polyhedron =
      let man = Polka.manager_alloc_strict () in
      let exists x = Symbol.Map.mem x delta_map in
      let delta_constraints =
        Symbol.Map.fold (fun s diff xs ->
            (mk_eq srk (mk_const srk s) diff)::xs)
          delta_map
          []
      in
      Abstract.abstract ~exists srk man (mk_and srk (phi::delta_constraints))
      |> SrkApron.formula_of_property
    in
    let constraint_of_atom atom =
      match Formula.destruct srk atom with
      | `Atom (op, s, t) ->
        let t = V.sub (Linear.linterm_of srk t) (Linear.linterm_of srk s) in
        let (k, t) = V.pivot Linear.const_dim t in
        let term = substitute_map srk delta_map (Linear.of_linterm srk t) in
        begin match op with
          | `Leq | `Lt -> (term, `Geq, QQ.negate k)
          | `Eq -> (term, `Eq, QQ.negate k)
        end
      | _ -> assert false
    in
    match Formula.destruct srk delta_polyhedron with
      | `And xs -> List.map constraint_of_atom xs
      | `Tru -> []
      | `Fls -> [mk_real srk QQ.zero, `Eq, QQ.one]
      | _ -> [constraint_of_atom delta_polyhedron]

  let exp srk tr_symbols loop_counter lr =
    List.map (fun (delta, op, c) ->
        match op with
        | `Eq ->
          mk_eq srk (mk_mul srk [mk_real srk c; loop_counter]) delta
        | `Geq ->
          mk_leq srk (mk_mul srk [mk_real srk c; loop_counter]) delta)
      lr
    |> mk_and srk

  let equal _ _ _ _ = failwith "Not yet implemented"
  let join _ _ _ _ = failwith "Not yet implemented"
  let widen _ _ _ _ = failwith "Not yet implemented"
end

module Recurrence = struct
  type matrix_rec =
    { rec_transform : QQ.t array array;
      rec_add : QQXs.t array }

  let rec_empty =
    { rec_transform = Array.make 0 (Array.make 0 QQ.zero);
      rec_add = Array.make 0 QQXs.zero }

  (* Iteration domain element.  Recurrence equations have the form
     A_1 * x' = B_1 * A_1 * x + c_1
     ...
     A_n * x' = B_n * A_n * x + c_n

     where each A_i/B_i is a rational matrix and each c_i is a vector of
     polynomial over dimensions corresponding to constant terms and the rows
     of A_1 ... A_{i-1}.

     The list of B_i/c_i's is stored in rec_eq.  The list of A_is is stored
     implicitly in term_of_id, which associates integer identifiers with
     linear term (so term_of_id.(nb_constants) corresponds to the first row of
     A_1, term_of_id.(nb_constants+size(A_1)) corresponds to the first row of
     A_2, ...).  Similarly for inequations in rec_leq. *)
  type 'a t =
    { term_of_id : ('a term) array;
      nb_constants : int;
      rec_eq : matrix_rec list;
      rec_leq : matrix_rec list }

  let pp srk tr_symbols formatter iter =
    let post_map = post_map tr_symbols in
    let postify =
      let subst sym =
        if Symbol.Map.mem sym post_map then
          mk_const srk (Symbol.Map.find sym post_map)
        else
          mk_const srk sym
      in
      substitute_const srk subst
    in
    let pp_id formatter id =
      Term.pp srk formatter iter.term_of_id.(id)
    in
    let pp_rec cmp offset formatter recurrence =
      recurrence.rec_transform |> Array.iteri (fun i row ->
          let nonzero = ref false in
          Format.fprintf formatter "(%a) %s @[<hov 1>"
            (Term.pp srk) (postify iter.term_of_id.(offset + i))
            cmp;
          row |> Array.iteri (fun j coeff ->
              if not (QQ.equal coeff QQ.zero) then begin
                if !nonzero then
                  Format.fprintf formatter "@ + "
                else
                  nonzero := true;
                Format.fprintf formatter "(%a)*(%a)"
                  QQ.pp coeff
                  (Term.pp srk) (iter.term_of_id.(offset + j))
              end
            );
          if !nonzero then
            Format.fprintf formatter "@ + ";
          Format.fprintf formatter "%a@]@;"
            (QQXs.pp pp_id) recurrence.rec_add.(i))
    in
    let offset =
      List.fold_left (fun offset recurrence ->
          pp_rec "=" offset formatter recurrence;
          (Array.length recurrence.rec_transform + offset))
        iter.nb_constants
        iter.rec_eq
    in
    ignore (List.fold_left (fun offset recurrence ->
        pp_rec "<=" offset formatter recurrence;
        (Array.length recurrence.rec_transform + offset))
        offset
        iter.rec_leq);
    Format.fprintf formatter "@]@]}"

  exception Not_a_polynomial

  (* Extract a stratified system of matrix recurrences *)
  let extract_matrix_eq srk wedge rec_sym term_of_id =
    let cs = Wedge.coordinate_system wedge in
    let post_coord_map =
      (* map pre-state coordinates to their post-state counterparts *)
      List.fold_left
        (fun map (sym, sym') ->
           try
             let coord = CS.cs_term_id cs (`App (sym, [])) in
             let coord' = CS.cs_term_id cs (`App (sym', [])) in
             IntMap.add coord coord' map
           with Not_found -> map)
        IntMap.empty
        rec_sym
    in

    (* Detect stratified recurrences *)
    let rec fix rec_ideal =
      let offset = DArray.length term_of_id in
      logf "New stratum (%d recurrence terms)" (DArray.length term_of_id);
      let (mA,mB,rec_add) =
        extract_affine_transformation srk wedge rec_sym term_of_id rec_ideal
      in
      let size = Array.length rec_add in
      if size = 0 then
        []
      else
        let rec_transform =
          Array.init size (fun row ->
              Array.init size (fun col ->
                  QQMatrix.entry row col mB))
        in
        let rec_ideal' = ref rec_ideal in
        for i = 0 to size - 1 do
          DArray.add term_of_id (CS.term_of_vec cs (QQMatrix.row i mA))
        done;
        for i = 0 to size - 1 do
          let rec_eq =
            let lhs =
              QQXs.of_vec ~const:CS.const_id (QQMatrix.row i mA)
              |> QQXs.substitute (fun coord ->
                  assert (IntMap.mem coord post_coord_map);
                  QQXs.of_dim (IntMap.find coord post_coord_map))
            in
            let add =
              QQXs.substitute (fun i ->
                  (CS.polynomial_of_term cs (DArray.get term_of_id i)))
                rec_add.(i)
            in
            let rhs =
              BatEnum.fold (fun p (coeff, i) ->
                  if i = CS.const_id then
                    QQXs.add (QQXs.scalar coeff) p
                  else
                    QQXs.add p
                      (QQXs.scalar_mul coeff
                         (CS.polynomial_of_term cs
                            (DArray.get term_of_id (offset + i)))))
                QQXs.zero
                (V.enum (QQMatrix.row i mB))
              |> QQXs.add add
            in
            QQXs.add lhs (QQXs.negate rhs)
          in
          rec_ideal' := rec_eq::(!rec_ideal')
        done;
        { rec_transform; rec_add }::(fix (!rec_ideal'))
    in
    fix []

  (* Extract a stratified system of matrix recurrences *)
  let extract_periodic_rational_matrix_eq srk wedge rec_sym term_of_id =
    let cs = Wedge.coordinate_system wedge in
    let post_coord_map =
      (* map pre-state coordinates to their post-state counterparts *)
      List.fold_left
        (fun map (sym, sym') ->
           try
             let coord = CS.cs_term_id cs (`App (sym, [])) in
             let coord' = CS.cs_term_id cs (`App (sym', [])) in
             IntMap.add coord coord' map
           with Not_found -> map)
        IntMap.empty
        rec_sym
    in

    (* Detect stratified recurrences *)
    let rec fix rec_ideal =
      let offset = DArray.length term_of_id in
      logf "New stratum (%d recurrence terms)" (DArray.length term_of_id);
      let (mA,mB,rec_add) =
        extract_affine_transformation srk wedge rec_sym term_of_id rec_ideal
      in

      let dims = SrkUtil.Int.Set.elements (QQMatrix.row_set mA) in
      let prsd = Linear.periodic_rational_spectral_decomposition mB dims in
      let mU =
        BatList.fold_lefti (fun m i (p,lambda,v) ->
            QQMatrix.add_row i v m)
          QQMatrix.zero
          prsd
      in

      let mUA = QQMatrix.mul mU mA in
      let mUBA = QQMatrix.mul mU (QQMatrix.mul mB mA) in
      let mB = match Linear.divide_right mUBA mUA with
        | Some x -> x
        | None -> assert false
      in
      let mA = mUA in
      let rec_add = matrix_polyvec_mul mU rec_add in

      let size = Array.length rec_add in
      if size = 0 then
        []
      else
        let rec_transform =
          Array.init size (fun row ->
              Array.init size (fun col ->
                  QQMatrix.entry row col mB))
        in
        let rec_ideal' = ref rec_ideal in
        for i = 0 to size - 1 do
          DArray.add term_of_id (CS.term_of_vec cs (QQMatrix.row i mA))
        done;
        for i = 0 to size - 1 do
          let rec_eq =
            let lhs =
              QQXs.of_vec ~const:CS.const_id (QQMatrix.row i mA)
              |> QQXs.substitute (fun coord ->
                  assert (IntMap.mem coord post_coord_map);
                  QQXs.of_dim (IntMap.find coord post_coord_map))
            in
            let add =
              QQXs.substitute (fun i ->
                  (CS.polynomial_of_term cs (DArray.get term_of_id i)))
                rec_add.(i)
            in
            let rhs =
              BatEnum.fold (fun p (coeff, i) ->
                  if i = CS.const_id then
                    QQXs.add (QQXs.scalar coeff) p
                  else
                    QQXs.add p
                      (QQXs.scalar_mul coeff
                         (CS.polynomial_of_term cs
                            (DArray.get term_of_id (offset + i)))))
                QQXs.zero
                (V.enum (QQMatrix.row i mB))
              |> QQXs.add add
            in
            QQXs.add lhs (QQXs.negate rhs)
          in
          rec_ideal' := rec_eq::(!rec_ideal')
        done;
        { rec_transform; rec_add }::(fix (!rec_ideal'))
    in
    fix []

  (* Extract stratified recurrences of the form x' = x + p, where p is a
     polynomial over induction variables of lower strata *)
  let extract_induction_vars srk wedge tr_symbols rec_terms =
    let cs = Wedge.coordinate_system wedge in

    let id_of_sym sym =
      try
        CS.cs_term_id cs (`App (sym, []))
      with Not_found -> assert false
    in

    (* An additive dimension is one that is allowed to appear as an additive
       term *)
    let cs_dim = CS.dim cs in
    let additive_dim x = x >= cs_dim in

    let rewrite =
      let elim_order =
        Monomial.block [not % additive_dim] Monomial.degrevlex
      in
      let rewrite =
        ref (Polynomial.Rewrite.mk_rewrite elim_order (Wedge.vanishing_ideal wedge)
             |> Polynomial.Rewrite.grobner_basis)
      in
      rec_terms |> DArray.iteri (fun i t ->
          let vec = CS.vec_of_term cs t in
          let p =
            QQXs.add_term
              (QQ.of_int (-1))
              (Monomial.singleton (i + cs_dim) 1)
              (QQXs.of_vec ~const:(CS.const_id) vec)
          in
          rewrite := (Polynomial.Rewrite.add_saturate (!rewrite) p));
        rewrite
    in
    let recurrences = ref [] in
    let transform_one = [|[|QQ.one|]|] in
    let delta s s' = (* s' - s *)
      QQXs.sub
        (QQXs.of_dim (id_of_sym s'))
        (QQXs.of_dim (id_of_sym s))
    in
    let add_recurrence s s' add =
      let polynomial =
        QQXs.sub
          (QQXs.of_dim (id_of_sym s))
          (QQXs.of_dim (cs_dim + (DArray.length rec_terms)))
      in
      let recur =
        { rec_transform = transform_one;
          rec_add = [|add|] }
      in
      DArray.add rec_terms (mk_const srk s);
      rewrite := (Polynomial.Rewrite.add_saturate (!rewrite) polynomial);
      recurrences := recur::(!recurrences)
    in
    let subst x =
      if additive_dim x then
        QQXs.of_dim (x - cs_dim)
      else
        raise IllFormedRecurrence
    in
    let continue = ref true in
    let non_induction = ref tr_symbols in
    while !continue do
      continue := false;
      non_induction :=
        List.filter (fun (s,s') ->
            try
              let add =
                delta s s'
                |> Polynomial.Rewrite.reduce (!rewrite)
                |> QQXs.substitute subst
              in
              add_recurrence s s' add;
              continue := true;
              false
            with IllFormedRecurrence -> true)
          (!non_induction)
    done;
    List.rev (!recurrences)

  (* Extract recurrences of the form t' <= t + p, where p is a polynomial over
     recurrence terms *)
  let extract_vector_leq srk wedge tr_symbols term_of_id =
    (* For each transition symbol (x,x'), allocate a symbol delta_x, which is
       constrained to be equal to x'-x.  For each recurrence term t, allocate
       a symbol add_t, which is constrained to be equal to (the pre-state
       value of) t.  After projecting out all variables *except* the delta and
       add variables, we have a wedge where each constraint corresponds to a
       recurrence inequation. *)
    let delta =
      List.map (fun (s,_) ->
          let name = "delta_" ^ (show_symbol srk s) in
          mk_symbol srk ~name (typ_symbol srk s))
        tr_symbols
    in
    let add =
      DArray.map (fun t ->
          let name = "a[" ^ (Term.show srk t) ^ "]" in
          mk_symbol srk ~name (term_typ srk t :> typ))
        term_of_id
    in
    let delta_map =
      List.fold_left2 (fun map delta (s,s') ->
          Symbol.Map.add delta (mk_const srk s) map)
        Symbol.Map.empty
        delta
        tr_symbols
    in
    let add_map =
      BatEnum.fold
        (fun map i ->
           Symbol.Map.add (DArray.get add i) (QQXs.of_dim i) map)
        Symbol.Map.empty
        (0 -- (DArray.length add - 1))
    in
    let add_symbols =
      DArray.fold_right Symbol.Set.add add Symbol.Set.empty
    in
    let diff_symbols =
      List.fold_right Symbol.Set.add delta add_symbols
    in
    let constraints =
      (List.map2 (fun delta (s,s') ->
           mk_eq srk
             (mk_const srk delta)
             (mk_sub srk (mk_const srk s') (mk_const srk s)))
          delta
          tr_symbols)
      @ (BatEnum.map
           (fun i ->
              mk_eq srk
                (mk_const srk (DArray.get add i))
                (DArray.get term_of_id i))
           (0 -- ((DArray.length add) - 1))
         |> BatList.of_enum)
      @ (Wedge.to_atoms wedge)
    in
    (* Wedge over delta and add variables *)
    let diff_wedge =
      let subterm x = Symbol.Set.mem x add_symbols in
      Wedge.of_atoms srk constraints
      |> Wedge.exists ~subterm (fun x -> Symbol.Set.mem x diff_symbols)
    in
    let diff_cs = Wedge.coordinate_system diff_wedge in
    let transform_one = [|[|QQ.one|]|] in
    let recurrences = ref [] in
    let add_recurrence = function
      | (`Eq, _) ->
        (* Skip equations -- we assume that all recurrence equations have
           already been extracted. *)
        ()
      | (`Geq, t) ->
        (* Rewrite t>=0 as (rec_term'-rec_term) <= rec_add, where rec_term is a
           linear term and rec_add is a polynomial over recurrence terms of
           lower strata. *)
        let (c, t) = V.pivot Linear.const_dim t in
        let (rec_term, rec_add) =
          BatEnum.fold
            (fun (rec_term, rec_add) (coeff, coord) ->
               let diff_term = CS.term_of_coordinate diff_cs coord in
               match Term.destruct srk diff_term with
               | `App (sym, []) when Symbol.Map.mem sym delta_map ->
                 let term =
                   mk_mul srk [mk_real srk (QQ.negate coeff);
                               Symbol.Map.find sym delta_map]
                 in
                 (term::rec_term, rec_add)
               | _ ->
                 let to_mvp = function
                   | `App (sym, []) ->
                     (try Symbol.Map.find sym add_map
                      with Not_found -> assert false)
                   | `Real k -> QQXs.scalar k
                   | `Add xs -> List.fold_left QQXs.add QQXs.zero xs
                   | `Mul xs -> List.fold_left QQXs.mul QQXs.one xs
                   | _ -> raise Not_a_polynomial
                 in
                 let term =
                   QQXs.scalar_mul coeff (Term.eval srk to_mvp diff_term)
                 in
                 (rec_term, QQXs.add term rec_add))
            ([], QQXs.scalar c)
            (V.enum t)
        in
        if rec_term != [] then
          let recurrence =
            { rec_transform = transform_one;
              rec_add = [|rec_add|] }
          in
          recurrences := recurrence::(!recurrences);
          DArray.add term_of_id (mk_add srk rec_term);
    in
    let add_recurrence x =
      try add_recurrence x
      with Not_a_polynomial -> ()
    in
    List.iter add_recurrence (Wedge.polyhedron diff_wedge);
    List.rev (!recurrences)

  (* Extract a system of recurrencs of the form Ax' <= BAx + b, where B has
     only positive entries and b is a vector of polynomials in recurrence terms
     at lower strata. *)
  let extract_matrix_leq srk wedge tr_symbols term_of_id =
    let open Apron in
    let cs = Wedge.coordinate_system wedge in
    let man = Polka.manager_alloc_loose () in
    let coeff_of_qq = Coeff.s_of_mpqf in
    let qq_of_coeff = function
      | Coeff.Scalar (Scalar.Float k) -> QQ.of_float k
      | Coeff.Scalar (Scalar.Mpqf k)  -> k
      | Coeff.Scalar (Scalar.Mpfrf k) -> Mpfrf.to_mpqf k
      | Coeff.Interval _ -> assert false
    in
    let linexpr_of_vec vec =
      let mk (coeff, id) = (coeff_of_qq coeff, id) in
      let (const_coeff, rest) = V.pivot CS.const_id vec in
      Linexpr0.of_list None
        (BatList.of_enum (BatEnum.map mk (V.enum rest)))
        (Some (coeff_of_qq const_coeff))
    in
    let vec_of_linexpr linexpr =
      let vec = ref V.zero in
      linexpr |> Linexpr0.iter (fun coeff dim ->
          vec := V.add_term (qq_of_coeff coeff) dim (!vec));
      V.add_term (qq_of_coeff (Linexpr0.get_cst linexpr)) CS.const_id (!vec)
    in

    let tr_coord =
      try
        List.map (fun (s,s') ->
            (CS.cs_term_id cs (`App (s, [])),
             CS.cs_term_id cs (`App (s', []))))
          tr_symbols
        |> Array.of_list
      with Not_found -> assert false
    in

    let rec fix polyhedron =
      let open Lincons0 in
      (* Polyhedron is of the form Ax' <= Bx + Cy, or equivalently,
         [-A B C]*[x' x y] >= 0. constraints is an array consisting of the
         rows of [-A B C].  *)
      logf "Polyhedron: %a"
        (Abstract0.print
           ((SrkUtil.mk_show (Term.pp srk)) % CS.term_of_coordinate cs))
        polyhedron;
      let constraints = DArray.create () in
      Abstract0.to_lincons_array man polyhedron
      |> Array.iter (fun lincons ->
          let vec = vec_of_linexpr lincons.linexpr0 in
          DArray.add constraints vec;
          if lincons.typ = EQ then
            DArray.add constraints (V.negate vec));
      let nb_constraints = DArray.length constraints in

      (* vu_cone is the cone { [v u] : u >= 0, v >= 0 uA = vB } *)
      let vu_cone =
        let pos_constraints = (* u >= 0, v >= 0 *)
          Array.init (2 * nb_constraints) (fun i ->
              Lincons0.make
                (Linexpr0.of_list None [(coeff_of_qq QQ.one, i)] None)
                SUPEQ)
          |> Abstract0.of_lincons_array man 0 (2 * nb_constraints)
        in
        Array.init (Array.length tr_coord) (fun i ->
            let (pre, post) = tr_coord.(i) in
            let linexpr = Linexpr0.make None in
            for j = 0 to nb_constraints - 1 do
              let vec = DArray.get constraints j in
              Linexpr0.set_coeff linexpr j (coeff_of_qq (V.coeff pre vec));
              Linexpr0.set_coeff
                linexpr
                (j + nb_constraints)
                (coeff_of_qq (V.coeff post vec));
            done;
            Lincons0.make linexpr Lincons0.EQ)
        |> Abstract0.meet_lincons_array man pos_constraints
      in
      (* Project vu_cone onto the v dimensions and compute generators. *)
      let v_generators =
        Abstract0.remove_dimensions
          man
          vu_cone
          { Dim.dim =
              (Array.init nb_constraints (fun i -> nb_constraints + i));
            Dim.intdim = 0;
            Dim.realdim = nb_constraints }
        |> Abstract0.to_generator_array man
      in
      (* new_constraints is v_generators * [-A B C]*)
      let new_constraints =
        Array.fold_right (fun gen nc ->
            let open Generator0 in
            let vec = vec_of_linexpr gen.linexpr0 in
            let row =
              BatEnum.fold (fun new_row (coeff, dim) ->
                  assert (dim < nb_constraints);
                  V.scalar_mul coeff (DArray.get constraints dim)
                  |> V.add new_row)
                V.zero
                (V.enum vec)
              |> linexpr_of_vec
            in
            assert (QQ.equal QQ.zero (V.coeff CS.const_id vec));
            if gen.typ = RAY then
              (Lincons0.make row Lincons0.SUPEQ)::nc
            else if gen.typ = VERTEX then begin
              assert (V.equal V.zero vec); (* should be the origin *)
              nc
            end else
              assert false)
          v_generators
          []
        |> Array.of_list
      in
      let new_polyhedron =
        Abstract0.of_lincons_array man 0 (CS.dim cs) new_constraints
      in
      if Abstract0.is_eq man polyhedron new_polyhedron then
        if nb_constraints = 0 then
          (QQMatrix.zero,
           Array.make 0 (Array.make 0 QQ.zero),
           Array.make 0 QQXs.zero)
        else
          let mA =
            BatEnum.fold (fun mA i ->
                let row =
                  BatEnum.fold (fun row j ->
                      let (pre, post) = tr_coord.(j) in
                      V.add_term
                        (QQ.negate (V.coeff post (DArray.get constraints i)))
                        pre
                        row)
                    V.zero
                    (0 -- (Array.length tr_coord - 1))
                in
                QQMatrix.add_row i row mA)
              QQMatrix.zero
              (0 -- (nb_constraints - 1))
          in

          (* Find a non-negative M such that B=M*A *)
          let m_entries = (* corresponds to one generic row of M *)
            Array.init nb_constraints (fun i -> mk_symbol srk `TyReal)
          in
          (* Each entry of M must be non-negative *)
          let pos_constraints =
            List.map (fun sym ->
                mk_leq srk (mk_real srk QQ.zero) (mk_const srk sym))
              (Array.to_list m_entries)
          in
          let m_times_a =
            (0 -- (Array.length tr_coord - 1))
            /@ (fun i ->
                let (pre, post) = tr_coord.(i) in
                (0 -- (nb_constraints - 1))
                /@ (fun j ->
                    mk_mul srk [mk_const srk m_entries.(j);
                                mk_real srk (QQMatrix.entry j pre mA)])
                |> BatList.of_enum
                |> mk_add srk)
            |> BatArray.of_enum
          in
          (* B[i,j] = M[i,1]*A[1,j] + ... + M[i,n]*A[n,j] *)
          let mB =
            Array.init nb_constraints (fun i ->
                let row_constraints =
                  (0 -- (Array.length tr_coord - 1))
                  /@ (fun j ->
                      let (pre, post) = tr_coord.(j) in
                      mk_eq srk
                        m_times_a.(j)
                        (mk_real srk (V.coeff pre (DArray.get constraints i))))
                  |> BatList.of_enum
                in
                let s = Smt.mk_solver srk in
                Smt.Solver.add s pos_constraints;
                Smt.Solver.add s row_constraints;
                let model =
                  (* First try for a simple recurrence, then fall back *)
                  Smt.Solver.push s;
                  (0 -- (Array.length m_entries - 1))
                  /@ (fun j ->
                      if i = j then
                        mk_true srk
                      else
                        mk_eq srk
                          (mk_const srk m_entries.(j))
                          (mk_real srk QQ.zero))
                  |> BatList.of_enum
                  |> Smt.Solver.add s;
                  match Smt.Solver.get_model s with
                  | `Sat model -> model
                  | _ ->
                    Smt.Solver.pop s 1;
                    match Smt.Solver.get_model s with
                    | `Sat model -> model
                    | _ -> assert false
                in
                Array.init nb_constraints (fun i ->
                    Interpretation.real model m_entries.(i)))
          in
          let pvc =
            Array.init nb_constraints (fun i ->
                QQXs.scalar (V.coeff CS.const_id (DArray.get constraints i)))
          in
          (mA,mB,pvc)
      else
        fix (Abstract0.widening man polyhedron new_polyhedron)
    in
    (* TODO: reduce each halfspace *)
    let polyhedron =
      let constraints =
        BatList.filter_map
          (function
            | (`Eq, vec) ->
              Some (Lincons0.make (linexpr_of_vec vec) Lincons0.EQ)
            | (`Geq, vec) ->
              Some (Lincons0.make (linexpr_of_vec vec) Lincons0.SUPEQ))
          (Wedge.polyhedron wedge)
        |> Array.of_list
      in
      Abstract0.of_lincons_array
        man
        0
        (CS.dim cs)
        constraints
    in
    let tr_coord_set =
      Array.fold_left
        (fun set (d,d') -> IntSet.add d (IntSet.add d' set))
        IntSet.empty
        tr_coord
    in
    let forget =
      let non_tr_coord =
        BatEnum.fold (fun non_tr dim ->
            if IntSet.mem dim tr_coord_set then
              non_tr
            else
              dim::non_tr)
          []
          (0 -- (CS.dim cs - 1))
      in
      Array.of_list (List.rev non_tr_coord)
    in
    let polyhedron =
      Abstract0.forget_array
        man
        polyhedron
        forget
        false
    in
    let (mA, rec_transform, rec_add) = fix polyhedron in
    let size = Array.length rec_add in
    for i = 0 to size - 1 do
      DArray.add term_of_id (CS.term_of_vec cs (QQMatrix.row i mA))
    done;
    [{ rec_transform; rec_add }]

  let abstract_iter_wedge extract_eq extract_leq srk tr_symbols wedge =
    logf "--------------- Abstracting wedge ---------------@\n%a)" Wedge.pp wedge;
    let cs = Wedge.coordinate_system wedge in
    let pre_symbols = pre_symbols tr_symbols in
    let post_symbols = post_symbols tr_symbols in
    tr_symbols |> List.iter (fun (s,s') ->
        CS.admit_cs_term cs (`App (s, []));
        CS.admit_cs_term cs (`App (s', [])));

    let term_of_id = DArray.create () in

    (* Detect constant terms *)
    let is_symbolic_constant x =
      not (Symbol.Set.mem x pre_symbols || Symbol.Set.mem x post_symbols)
    in
    let constant_symbols =
      ref (Symbol.Set.of_list [get_named_symbol srk "log";
                               get_named_symbol srk "pow"])
    in
    for i = 0 to CS.dim cs - 1 do
      let term = CS.term_of_coordinate cs i in
      match Term.destruct srk term with
      | `App (sym, []) ->
        if is_symbolic_constant sym then begin
          constant_symbols := Symbol.Set.add sym (!constant_symbols);
          DArray.add term_of_id term
        end
      | _ ->
        if Symbol.Set.subset (symbols term) (!constant_symbols) then
          DArray.add term_of_id term
    done;
    let nb_constants = DArray.length term_of_id in
    let rec_eq = extract_eq srk wedge tr_symbols term_of_id in
    let rec_leq = extract_leq srk wedge tr_symbols term_of_id in
    let result =
    { nb_constants;
      term_of_id = DArray.to_array term_of_id;
      rec_eq = rec_eq;
      rec_leq = rec_leq }
    in
    logf "=============== Wedge/Matrix recurrence ===============@\n%a)"
      (pp srk tr_symbols) result;
    result

  let abstract_iter extract_eq extract_leq ?(exists=fun x -> true) srk symbols phi =
    let post_symbols = post_symbols symbols in
    let subterm x = not (Symbol.Set.mem x post_symbols) in
    let wedge =
      Wedge.abstract ~exists ~subterm srk phi
    in
    abstract_iter_wedge extract_eq extract_leq srk symbols wedge

  let exp srk tr_symbols loop_counter iter =
    let open Ocrs in
    let open Type_def in

    Nonlinear.ensure_symbols srk;

    let post_map = (* map pre-state vars to post-state vars *)
      post_map tr_symbols
    in

    let postify =
      let subst sym =
        if Symbol.Map.mem sym post_map then
          mk_const srk (Symbol.Map.find sym post_map)
        else
          mk_const srk sym
      in
      substitute_const srk subst
    in

    (* pre/post subscripts *)
    let ss_pre = SSVar "k" in
    let ss_post = SAdd ("k", 1) in

    (* Map identifiers to their closed forms, so that they can be used in the
       additive term of recurrences at higher strata *)
    let cf =
      Array.make (Array.length iter.term_of_id) (Rational (Mpqf.to_mpq QQ.zero))
    in
    for i = 0 to iter.nb_constants - 1 do
      cf.(i) <- Symbolic_Constant (string_of_int i)
    done;
    let term_of_expr =
      let pre_term_of_id name =
        iter.term_of_id.(int_of_string name)
      in
      let post_term_of_id name =
        let id = int_of_string name in
        postify (iter.term_of_id.(id))
      in
      term_of_ocrs srk loop_counter pre_term_of_id post_term_of_id
    in
    let close_matrix_rec recurrence offset =
      let size = Array.length recurrence.rec_add in
      let dim_vec = Array.init size (fun i -> string_of_int (offset+i)) in
      let ocrs_transform =
        Array.map (Array.map Mpqf.to_mpq) recurrence.rec_transform
      in
      let ocrs_add =
        Array.init size (fun i ->
            let cf_monomial m =
              Monomial.enum m
              /@ (fun (id, pow) -> Pow (cf.(id), Rational (Mpq.of_int pow)))
              |> BatList.of_enum
            in
            QQXs.enum recurrence.rec_add.(i)
            /@ (fun (coeff, m) ->
                Product (Rational (Mpqf.to_mpq coeff)::(cf_monomial m)))
            |> (fun x -> Sum (BatList.of_enum x)))
      in
      let recurrence_closed =
        let mat_rec =
          VEquals (Ovec (dim_vec, ss_post),
                   ocrs_transform,
                   Ovec (dim_vec, ss_pre),
                   ocrs_add)
        in
        logf "Matrix recurrence:@\n%s" (Mat_helpers.matrix_rec_to_string mat_rec);
        Log.time "OCRS" (Ocrs.solve_mat_recurrence mat_rec) false
      in
      recurrence_closed
    in
    let mk_int k = mk_real srk (QQ.of_int k) in
    let rec close mk_compare offset closed = function
      | [] -> (mk_and srk closed, offset)
      | (recurrence::rest) ->
        let size = Array.length recurrence.rec_add in
        let recurrence_closed = close_matrix_rec recurrence offset in
        let to_formula ineq =
          let PieceWiseIneq (ivar, pieces) = Deshift.deshift_ineq ineq in
          assert (ivar = "k");
          let piece_to_formula (ivl, ineq) =
            let hypothesis = match ivl with
              | Bounded (lo, hi) ->
                mk_and srk [mk_leq srk (mk_int lo) loop_counter;
                                 mk_leq srk loop_counter (mk_int hi)]
              | BoundBelow lo -> 
                mk_and srk [mk_leq srk (mk_int lo) loop_counter]
            in
            let conclusion = match ineq with
              | Equals (x, y) -> mk_compare srk (term_of_expr x) (term_of_expr y)
              | _ -> assert false
            in
            mk_if srk hypothesis conclusion
          in
          mk_and srk (List.map piece_to_formula pieces)
        in
        recurrence_closed |> List.iteri (fun i ineq ->
            match ineq with
            | Equals (x, y) -> cf.(offset + i) <- y
            | _ -> assert false);
        let recurrence_closed_formula = List.map to_formula recurrence_closed in
        close mk_compare (offset + size) (recurrence_closed_formula@closed) rest
    in
    let (closed_eq, offset) = close mk_eq iter.nb_constants [] iter.rec_eq in
    let (closed_leq, _) = close mk_leq offset [] iter.rec_leq in
    mk_and srk [closed_eq; closed_leq]


  let wedge_of srk tr_symbols iter =
    let post_map =
      List.fold_left
        (fun map (sym, sym') -> Symbol.Map.add sym sym' map)
        Symbol.Map.empty
        tr_symbols
    in
    let postify =
      let subst sym =
        if Symbol.Map.mem sym post_map then
          mk_const srk (Symbol.Map.find sym post_map)
        else
          mk_const srk sym
      in
      substitute_const srk subst
    in
    let rec_atoms mk_compare offset recurrence =
      recurrence.rec_transform |> Array.mapi (fun i row ->
          let term = iter.term_of_id.(offset + i) in
          let rhs_add =
            QQXs.term_of
              srk
              (fun j -> iter.term_of_id.(j))
              recurrence.rec_add.(i)
          in
          let rhs =
            BatArray.fold_lefti (fun rhs j coeff ->
                if QQ.equal coeff QQ.zero then
                  rhs
                else
                  let jterm =
                    mk_mul srk [mk_real srk coeff;
                                     iter.term_of_id.(offset + j)]
                  in
                  jterm::rhs)
              [rhs_add]
              row
            |> mk_add srk
          in
          mk_compare (postify term) rhs)
      |> BatArray.to_list
    in
    let (offset, atoms) =
      BatList.fold_left (fun (offset, atoms) recurrence ->
          let size = Array.length recurrence.rec_add in
          (offset+size,
           (rec_atoms (mk_eq srk) offset recurrence)@atoms))
        (iter.nb_constants, [])
        iter.rec_eq
    in
    let (_, atoms) =
      BatList.fold_left (fun (offset, atoms) recurrence ->
          let size = Array.length recurrence.rec_add in
          (offset+size,
           (rec_atoms (mk_leq srk) offset recurrence)@atoms))
        (offset, atoms)
        iter.rec_leq
    in
    Wedge.of_atoms srk atoms

  let equal srk tr_symbols iter iter' =
    Wedge.equal (wedge_of srk tr_symbols iter) (wedge_of srk tr_symbols iter')
end

module SolvablePolynomialOne = struct
  include Recurrence

  let abstract_wedge srk tr_symbols wedge =
    abstract_iter_wedge extract_induction_vars extract_vector_leq srk tr_symbols wedge

  let abstract ?(exists=fun x -> true) srk =
    abstract_iter extract_induction_vars extract_vector_leq ~exists srk

  let join srk tr_symbols iter iter' =
    Wedge.join (wedge_of srk tr_symbols iter) (wedge_of srk tr_symbols iter')
    |> abstract_iter_wedge extract_induction_vars extract_vector_leq srk tr_symbols

  let widen srk tr_symbols iter iter' =
    Wedge.widen (wedge_of srk tr_symbols iter) (wedge_of srk tr_symbols iter')
    |> abstract_iter_wedge extract_induction_vars extract_vector_leq srk tr_symbols
end

module SolvablePolynomial = struct
  include Recurrence

  let abstract_wedge srk tr_symbols wedge =
    abstract_iter_wedge extract_matrix_eq extract_vector_leq srk tr_symbols wedge

  let abstract ?(exists=fun x -> true) srk =
    abstract_iter extract_matrix_eq extract_vector_leq ~exists srk

  let join srk tr_symbols iter iter' =
    Wedge.join (wedge_of srk tr_symbols iter) (wedge_of srk tr_symbols iter')
    |> abstract_iter_wedge extract_matrix_eq extract_vector_leq srk tr_symbols

  let widen srk tr_symbols iter iter' =
    Wedge.widen (wedge_of srk tr_symbols iter) (wedge_of srk tr_symbols iter')
    |> abstract_iter_wedge extract_matrix_eq extract_vector_leq srk tr_symbols
end

module SolvablePolynomialPeriodicRational = struct
  include Recurrence

  (* Given a matrix in which each vector in the standard basis is a
     periodic generalized eigenvector, find a PRSD over the standard
     basis. *)
  let standard_basis_prsd mA size =
    let dims = BatList.of_enum (0 -- (size-1)) in
    let new_prsd =
      List.rev (Linear.periodic_rational_spectral_decomposition mA dims)
    in
    let id = QQMatrix.identity dims in
    let get_period_eigenvalue v =
      let (p, lambda, _) =
        BatList.find (fun (p, lambda, _) ->
            V.is_zero
              (Linear.vector_left_mul v
                 (QQMatrix.exp
                    (QQMatrix.add
                       (QQMatrix.exp mA p)
                       (QQMatrix.scalar_mul (QQ.negate lambda) id))
                    size)))
          new_prsd
      in
      (p, lambda)
    in
    (0 -- (size - 1))
    /@ (fun i ->
        let v = V.of_term QQ.one i in
        let (p, lambda) = get_period_eigenvalue v in
        (p, lambda, v))
    |> BatList.of_enum

  let abstract_wedge srk tr_symbols wedge =
    abstract_iter_wedge extract_periodic_rational_matrix_eq extract_vector_leq srk tr_symbols wedge

  let abstract ?(exists=fun x -> true) srk =
    abstract_iter extract_periodic_rational_matrix_eq extract_vector_leq ~exists srk

  let exp srk tr_symbols loop_counter iter =
    Nonlinear.ensure_symbols srk;

    let srk = srk in

    let post_map = (* map pre-state vars to post-state vars *)
      post_map tr_symbols
    in

    let postify =
      let subst sym =
        if Symbol.Map.mem sym post_map then
          mk_const srk (Symbol.Map.find sym post_map)
        else
          mk_const srk sym
      in
      substitute_const srk subst
    in

    (* Map identifiers to their closed forms, so that they can be used in the
       additive term of recurrences at higher strata *)
    let cf =
      Array.make (Array.length iter.term_of_id) UPXs.zero
    in
    (* Substitute closed forms in for a polynomial *)
    let substitute_closed_forms p =
      BatEnum.fold (fun up (coeff, m) ->
          BatEnum.fold (fun m_up (i, pow) ->
              UPXs.mul m_up (UPXs.exp cf.(i) pow))
            (UPXs.scalar (UP.make [] [ExpPolynomial.scalar coeff]))
            (Monomial.enum m)
          |> UPXs.add up)
        UPXs.zero
        (QQXs.enum p)
    in

    (* For each period p, maintain a pair (q, r) such that loop_counter = qp + r *)
    let qr_map = BatHashtbl.create 97 in
    Hashtbl.add qr_map 1 (loop_counter, mk_real srk QQ.zero);
    let get_qr n =
      if Hashtbl.mem qr_map n then
        Hashtbl.find qr_map n
      else
        let loop_q = mk_const srk (mk_symbol srk ~name:"q" `TyInt) in
        let loop_r = mk_const srk (mk_symbol srk ~name:"r" `TyInt) in
        Hashtbl.add qr_map n (loop_q, loop_r);
        (loop_q, loop_r)
    in

    (* Close constant terms *)
    for i = 0 to iter.nb_constants - 1 do
      cf.(i) <- UPXs.of_dim i
    done;

    let close_matrix_rec recurrence offset =
      let size = Array.length recurrence.rec_add in
      let transform = QQMatrix.of_dense recurrence.rec_transform in
      let prsd = standard_basis_prsd transform size in
      let rec_add_cf =
        Array.init (Array.length recurrence.rec_add) (fun i ->
            substitute_closed_forms recurrence.rec_add.(i))
      in

      prsd |> List.map (fun (p, lambda, v) ->

          (* v is a generalized eigenvector of transform^p.  Traverse
             the Jordan chain generated by v from the bottom up,
             computing closed forms along the way. *)
          let jordan_chain =
            Linear.jordan_chain (QQMatrix.exp transform p) lambda v
          in

          if QQ.equal lambda QQ.zero then begin
            assert (p == 1);
            BatList.fold_right (fun v cf ->
                let cf_transform =
                  BatEnum.fold (fun v_cf (coeff, i) ->
                      UPXs.add_term
                        (UP.make [coeff] [ExpPolynomial.zero])
                        (Monomial.singleton (offset + i) 1)
                        v_cf)
                    UPXs.zero
                    (V.enum v)
                in
                let cf_add =
                  UPXs.map_coeff
                    (fun _ -> UP.shift [QQ.zero])
                    (UPXs.add cf (vec_upxsvec_dot v rec_add_cf))
                in
                UPXs.add cf_transform cf_add)
              jordan_chain
              UPXs.zero
          end else begin
            List.fold_right (fun v cf ->

                let cf_transform =
                  let v_Ai = (* vA^0, ..., vA^{p-1} *)
                    BatEnum.fold (fun (v_transform, xs) i ->
                        let next = Linear.vector_left_mul v_transform transform in
                        (next, next::xs))
                      (v, [v])
                      (1 -- (p - 1))
                    |> snd
                    |> List.rev
                  in
                  BatEnum.fold (fun cf_A i ->
                      let period =
                        List.map (fun r ->
                            ExpPolynomial.of_term (QQX.scalar (V.coeff i r)) lambda)
                          v_Ai
                      in
                      let up = UP.make [] period in
                      UPXs.add_term
                        up
                        (Monomial.singleton (offset + i) 1)
                        cf_A)
                    UPXs.zero
                    (0 -- (size - 1))
                in

                let cf_add =
                  (0 -- (p - 1)) |> BatEnum.map (fun i ->
                      (* sum_{j=0}^{p-1} v * A^{p-j-1} * cf_add(pk+j+i) *)
                      let sum_pk_i =
                        BatEnum.fold (fun sum j ->
                            UPXs.add
                              sum
                              (vec_upxsvec_dot
                                 (Linear.vector_left_mul
                                    v
                                    (QQMatrix.exp transform (p-j-1)))
                                 (Array.map
                                    (UPXs.map_coeff (fun _ f ->
                                         UP.compose_left_affine f p (j+i)))
                                    rec_add_cf)))
                          UPXs.zero
                          (0 -- (p - 1))
                      in
                      (* sum_{j=0}^{i-1} v * A^{i-j-1} * cf_add(j) *)
                      let initial =
                        BatEnum.fold (fun sum j ->
                            let cf_add_j =
                              Array.map (fun f -> UPXs.eval f j) rec_add_cf
                            in
                            let vAij =
                              Linear.vector_left_mul
                                v
                                (QQMatrix.exp transform (i-j-1))
                            in
                            QQXs.add sum (vec_qqxsvec_dot vAij cf_add_j))
                          QQXs.zero
                          (0 -- (i-1))
                      in
                      let get_initial m = QQXs.coeff m initial in
                      UPXs.map_coeff
                        (fun m f -> UP.solve_rec ~initial:(get_initial m) lambda f)
                        (UPXs.add cf sum_pk_i))
                  |> BatList.of_enum
                  |> UPXs.flatten
                in

                UPXs.add cf_transform cf_add)
              jordan_chain
              UPXs.zero
          end)
    in

    let rec close mk_compare offset closed = function
      | [] -> (mk_and srk closed, offset)
      | (recurrence::rest) ->
        let size = Array.length recurrence.rec_add in
        let recurrence_closed = close_matrix_rec recurrence offset in
        let to_formula i closed =
          let lhs = postify iter.term_of_id.(offset + i) in
          let rhs =
            (UPXs.enum closed)
            /@ (fun (up, m) ->
                let m = Monomial.term_of srk (fun i -> iter.term_of_id.(i)) m in
                let (loop_q, loop_r) = get_qr (UP.period_len up) in
                let up = UP.term_of srk loop_q loop_r up in
                mk_mul srk [up; m])
            |> BatList.of_enum
            |> mk_add srk
          in
          mk_compare srk lhs rhs
        in

        recurrence_closed |> List.iteri (fun i closed ->
            cf.(offset + i) <- closed);

        let recurrence_closed_formula = BatList.mapi to_formula recurrence_closed in
        close mk_compare (offset + size) (recurrence_closed_formula@closed) rest
    in
    let (closed_eq, offset) = close mk_eq iter.nb_constants [] iter.rec_eq in
    let (closed_leq, _) = close mk_leq offset [] iter.rec_leq in
    let qr_constraints =
      Hashtbl.fold (fun n (q, r) rest ->
          if n = 0 then
            rest
          else
            let n = mk_real srk (QQ.of_int n) in
            (* loop_counter = qn + r /\ 0 <= r < n *)
            (mk_eq srk
               loop_counter
               (mk_add srk [mk_mul srk [q; n]; r]))
            ::(mk_lt srk r n)
            ::(mk_leq srk (mk_real srk QQ.zero) r)
            ::rest)
        qr_map
        []
      |> mk_and srk
    in
    mk_and srk [
      closed_eq;
      closed_leq;
      qr_constraints
    ]

  let join srk tr_symbols iter iter' =
    Wedge.join (wedge_of srk tr_symbols iter) (wedge_of srk tr_symbols iter')
    |> abstract_iter_wedge extract_periodic_rational_matrix_eq extract_vector_leq srk tr_symbols

  let widen srk tr_symbols iter iter' =
    Wedge.widen (wedge_of srk tr_symbols iter) (wedge_of srk tr_symbols iter')
    |> abstract_iter_wedge extract_periodic_rational_matrix_eq extract_vector_leq srk tr_symbols

end

module Product (A : PreDomain) (B : PreDomain) = struct
  type 'a t = 'a A.t * 'a B.t

  let pp srk tr_symbols formatter (a, b) =
    Format.fprintf formatter "%a@;%a"
      (A.pp srk tr_symbols) a
      (B.pp srk tr_symbols) b

  let exp srk tr_symbols loop_counter (a, b) =
    mk_and srk [A.exp srk tr_symbols loop_counter a;
                B.exp srk tr_symbols loop_counter b]

  let join srk tr_symbols (a, b) (a', b') =
    (A.join srk tr_symbols a a', B.join srk tr_symbols b b')

  let widen srk tr_symbols (a, b) (a', b') =
    (A.widen srk tr_symbols a a', B.widen srk tr_symbols b b')

  let equal srk tr_symbols (a, b) (a', b') =
    (A.equal srk tr_symbols a a')
    && (B.equal srk tr_symbols b b')

  let abstract ?(exists=fun x -> true) srk tr_symbols phi =
    (A.abstract ~exists srk tr_symbols phi,
     B.abstract ~exists srk tr_symbols phi)
end

module Sum (A : PreDomain) (B : PreDomain) () = struct
  type 'a t = Left of 'a A.t | Right of 'a B.t

  let abstract_left = ref true

  let pp srk tr_symbols formatter = function
    | Left a -> A.pp srk tr_symbols formatter a
    | Right b -> B.pp srk tr_symbols formatter b

  let left a = Left a

  let right b = Right b

  let exp srk tr_symbols loop_counter = function
    | Left a -> A.exp srk tr_symbols loop_counter a
    | Right b -> B.exp srk tr_symbols loop_counter b

  let join srk tr_symbols x y = match x,y with
    | Left x, Left y -> Left (A.join srk tr_symbols x y)
    | Right x, Right y -> Right (B.join srk tr_symbols x y)
    | _, _ -> invalid_arg "Join: incompatible elements"

  let widen srk tr_symbols x y = match x,y with
    | Left x, Left y -> Left (A.widen srk tr_symbols x y)
    | Right x, Right y -> Right (B.widen srk tr_symbols x y)
    | _, _ -> invalid_arg "Widen: incompatible elements"

  let equal srk tr_symbols x y = match x,y with
    | Left x, Left y -> A.equal srk tr_symbols x y
    | Right x, Right y -> B.equal srk tr_symbols x y
    | _, _ -> invalid_arg "Equal: incompatible elements"

  let abstract ?(exists=fun x -> true) srk tr_symbols phi =
    if !abstract_left then
      Left (A.abstract ~exists srk tr_symbols phi)
    else
      Right (B.abstract ~exists srk tr_symbols phi)
end

module Split (Iter : PreDomain) = struct
  type 'a t = ('a, typ_bool, 'a Iter.t * 'a Iter.t) Expr.Map.t

  let pp srk tr_symbols formatter split_iter =
    let pp_elt formatter (pred,(left,right)) =
      Format.fprintf formatter "[@[<v 0>%a@; %a@; %a@]]"
        (Formula.pp srk) pred
        (Iter.pp srk tr_symbols) left
        (Iter.pp srk tr_symbols) right
    in
    Format.fprintf formatter "<Split @[<v 0>%a@]>"
      (SrkUtil.pp_print_enum pp_elt) (Expr.Map.enum split_iter)

  (* Lower a split iter into an iter by picking an arbitary split and joining
     both sides. *)
  let lower_split srk tr_symbols split_iter =
    match BatEnum.get (Expr.Map.values split_iter) with
    | Some (iter, iter') -> Iter.join srk tr_symbols iter iter'
    | None -> assert false

  let base_bottom srk tr_symbols = Iter.abstract srk tr_symbols (mk_false srk)

  let lift_split srk tr_symbols iter =
    Expr.Map.add
      (mk_true srk)
      (iter, base_bottom srk tr_symbols)
      Expr.Map.empty

  let abstract ?(exists=fun x -> true) srk tr_symbols body =
    let post_symbols = post_symbols tr_symbols in
    let predicates =
      let preds = ref Expr.Set.empty in
      let prestate sym = exists sym && not (Symbol.Set.mem sym post_symbols) in
      let rr expr =
        match destruct srk expr with
        | `Not phi ->
          if Symbol.Set.for_all prestate (symbols phi) then
            preds := Expr.Set.add phi (!preds);
          expr
        | `Atom (op, s, t) ->
          let phi =
            match op with
            | `Eq -> mk_eq srk s t
            | `Leq -> mk_leq srk s t
            | `Lt -> mk_lt srk s t
          in
          begin
          if Symbol.Set.for_all prestate (symbols phi) then
            let redundant = match op with
              | `Eq -> false
              | `Leq -> Expr.Set.mem (mk_lt srk t s) (!preds)
              | `Lt -> Expr.Set.mem (mk_lt srk t s) (!preds)
            in
            if not redundant then
              preds := Expr.Set.add phi (!preds)
          end;
          expr
        | _ -> expr
      in
      ignore (rewrite srk ~up:rr body);
      BatList.of_enum (Expr.Set.enum (!preds))
    in
    let uninterp_body =
      rewrite srk
        ~up:(Nonlinear.uninterpret_rewriter srk)
        body
    in
    let solver = Smt.mk_solver srk in
    Smt.Solver.add solver [uninterp_body];
    let sat_modulo_body psi =
      let psi =
        rewrite srk
          ~up:(Nonlinear.uninterpret_rewriter srk)
          psi
      in
      Smt.Solver.push solver;
      Smt.Solver.add solver [psi];
      let result = Smt.Solver.check solver [] in
      Smt.Solver.pop solver 1;
      result
    in
    let is_split_predicate psi =
      (sat_modulo_body psi = `Sat)
      && (sat_modulo_body (mk_not srk psi) = `Sat)
    in
    let post_map =
      List.fold_left
        (fun map (s, s') ->
           Symbol.Map.add s (mk_const srk s') map)
        Symbol.Map.empty
        tr_symbols
    in
    let postify =
      let subst sym =
        if Symbol.Map.mem sym post_map then
          Symbol.Map.find sym post_map
        else
          mk_const srk sym
      in
      substitute_const srk subst
    in
    let add_split_predicate split_iter psi =
      if is_split_predicate psi then
        let not_psi = mk_not srk psi in
        let post_psi = postify psi in
        let post_not_psi = postify not_psi in
        let psi_body = mk_and srk [body; psi] in
        let not_psi_body = mk_and srk [body; not_psi] in
        if sat_modulo_body (mk_and srk [psi; post_not_psi]) = `Unsat then
          (* {psi} body {psi} -> body* = ([not psi]body)*([psi]body)* *)
          let left_abstract =
            Iter.abstract ~exists srk tr_symbols not_psi_body
          in
          let right_abstract =
            Iter.abstract ~exists srk tr_symbols psi_body
          in
          Expr.Map.add not_psi (left_abstract, right_abstract) split_iter
        else if sat_modulo_body (mk_and srk [not_psi; post_psi]) = `Unsat then
          (* {not phi} body {not phi} -> body* = ([phi]body)*([not phi]body)* *)
          let left_abstract =
            Iter.abstract ~exists srk tr_symbols psi_body
          in
          let right_abstract =
            Iter.abstract ~exists srk tr_symbols not_psi_body
          in
          Expr.Map.add psi (left_abstract, right_abstract) split_iter
        else
          split_iter
      else
        split_iter
    in
    let split_iter =
      List.fold_left add_split_predicate Expr.Map.empty predicates
    in
    (* If there are no predicates that can split the loop, split on true *)
    let split_iter =
      if Expr.Map.is_empty split_iter then
        Expr.Map.add
          (mk_true srk)
          (Iter.abstract ~exists srk tr_symbols body,
           base_bottom srk tr_symbols)
          Expr.Map.empty
      else
        split_iter
    in
    logf "abstract: %a" (Formula.pp srk) body;
    logf "iter: %a" (pp srk tr_symbols) split_iter;
    split_iter

  let sequence srk symbols phi psi =
    let (phi_map, psi_map) =
      List.fold_left (fun (phi_map, psi_map) (sym, sym') ->
          let mid_name = "mid_" ^ (show_symbol srk sym) in
          let mid_symbol =
            mk_symbol srk ~name:mid_name (typ_symbol srk sym)
          in
          let mid = mk_const srk mid_symbol in
          (Symbol.Map.add sym' mid phi_map,
           Symbol.Map.add sym mid psi_map))
        (Symbol.Map.empty, Symbol.Map.empty)
        symbols
    in
    let phi_subst symbol =
      if Symbol.Map.mem symbol phi_map then
        Symbol.Map.find symbol phi_map
      else
        mk_const srk symbol
    in
    let psi_subst symbol =
      if Symbol.Map.mem symbol psi_map then
        Symbol.Map.find symbol psi_map
      else
        mk_const srk symbol
    in
    mk_and srk [substitute_const srk phi_subst phi;
                substitute_const srk psi_subst psi]

  let exp srk tr_symbols loop_counter split_iter =
    Expr.Map.enum split_iter
    /@ (fun (predicate, (left, right)) ->
        let not_predicate = mk_not srk predicate in
        let left_counter = mk_const srk (mk_symbol srk ~name:"K" `TyInt) in
        let right_counter = mk_const srk (mk_symbol srk ~name:"K" `TyInt) in
        let left_closure =
          mk_and srk [Iter.exp srk tr_symbols left_counter left;
                      mk_or srk [mk_eq srk (mk_real srk QQ.zero) left_counter;
                                 predicate]]
        in
        let right_closure =
          mk_and srk [Iter.exp srk tr_symbols right_counter right;
                      mk_or srk [mk_eq srk (mk_real srk QQ.zero) right_counter;
                                 not_predicate]]
        in
        let left_right =
          sequence srk tr_symbols left_closure right_closure
        in
        mk_and srk [left_right;
                    mk_eq srk (mk_add srk [left_counter; right_counter]) loop_counter])
    |> BatList.of_enum
    |> mk_and srk

  let join srk tr_symbols split_iter split_iter' =
    let f _ a b = match a,b with
      | Some (a_left, a_right), Some (b_left, b_right) ->
        Some (Iter.join srk tr_symbols a_left b_left,
              Iter.join srk tr_symbols a_right b_right)
      | _, _ -> None
    in
    let split_join = Expr.Map.merge f split_iter split_iter' in
    if Expr.Map.is_empty split_join then
      lift_split srk tr_symbols
        (Iter.join srk tr_symbols
           (lower_split srk tr_symbols split_iter)
           (lower_split srk tr_symbols split_iter'))
    else
      split_join

  let widen srk tr_symbols split_iter split_iter' =
    let f _ a b = match a,b with
      | Some (a_left, a_right), Some (b_left, b_right) ->
        Some (Iter.widen srk tr_symbols a_left b_left,
              Iter.widen srk tr_symbols a_right b_right)
      | _, _ -> None
    in
    let split_widen = Expr.Map.merge f split_iter split_iter' in
    if Expr.Map.is_empty split_widen then
      lift_split srk tr_symbols
        (Iter.widen srk tr_symbols
           (lower_split srk tr_symbols split_iter)
           (lower_split srk tr_symbols split_iter))
    else
      split_widen

  let equal srk tr_symbols split_iter split_iter' =
    BatEnum.for_all
      (fun ((p,(l,r)), (p',(l',r'))) ->
         Formula.equal p p'
         && Iter.equal srk tr_symbols l l'
         && Iter.equal srk tr_symbols r r')
      (BatEnum.combine
         (Expr.Map.enum split_iter,
          Expr.Map.enum split_iter'))
end

module MakeDomain (Iter : PreDomain) = struct
  type 'a t =
    { srk : 'a context;
      tr_symbols : (symbol * symbol) list;
      iter : 'a Iter.t }

  let equal iter iter' =
    let srk = iter.srk in
    let tr_symbols = iter.tr_symbols in
    assert(iter.tr_symbols = iter'.tr_symbols);
    Iter.equal srk tr_symbols iter.iter iter'.iter

  let join iter iter' =
    let srk = iter.srk in
    let tr_symbols = iter.tr_symbols in
    assert(iter.tr_symbols = iter'.tr_symbols);
    let iter = Iter.join srk tr_symbols iter.iter iter'.iter in
    { srk; tr_symbols; iter }

  let widen iter iter' =
    let srk = iter.srk in
    let tr_symbols = iter.tr_symbols in
    assert(iter.tr_symbols = iter'.tr_symbols);
    let iter = Iter.widen srk tr_symbols iter.iter iter'.iter in
    { srk; tr_symbols; iter }

  let pp formatter iter =
    Format.fprintf formatter "{@[<v 1>%a@]}"
      (Iter.pp iter.srk iter.tr_symbols) iter.iter

  let closure iter =
    let srk = iter.srk in
    let loop_counter_sym = mk_symbol srk ~name:"K" `TyInt in
    let loop_counter = mk_const srk loop_counter_sym in
    mk_and srk [Iter.exp iter.srk iter.tr_symbols loop_counter iter.iter;
                mk_leq srk (mk_real srk QQ.zero) loop_counter]

  let abstract ?(exists=fun x -> true) srk tr_symbols body =
    let iter = Iter.abstract ~exists srk tr_symbols body in
    { srk; tr_symbols; iter }

  let tr_symbols iter = iter.tr_symbols
end

module ProductWedge (A : PreDomainWedge) (B : PreDomainWedge) = struct
  include Product(A)(B)

  let abstract_wedge srk tr_symbols wedge =
    (A.abstract_wedge srk tr_symbols wedge,
     B.abstract_wedge srk tr_symbols wedge)

  let abstract ?(exists=fun x -> true) srk tr_symbols phi =
    let post_symbols = post_symbols tr_symbols in
    let subterm x = not (Symbol.Set.mem x post_symbols) in
    let wedge = Wedge.abstract ~exists ~subterm srk phi in
    abstract_wedge srk tr_symbols wedge
end

module SumWedge (A : PreDomainWedge) (B : PreDomainWedge) () = struct
  include Sum(A)(B)()

  let abstract_wedge srk tr_symbols wedge =
    if !abstract_left then
      Left (A.abstract_wedge srk tr_symbols wedge)
    else
      Right (B.abstract_wedge srk tr_symbols wedge)
end

module Vas : Domain = struct
  include Interpretation
  include Smt
  module QQSet = Set.Make(QQ)


  type vas = {dim : (symbol * symbol); res : QQSet.t ; inc : QQSet.t}
  type vas_sum = Abstraction of vas | Bottom of (symbol * symbol) | Unknown of (symbol * symbol)
  type 'a t = {srk : 'a context; svvas : vas_sum list; symbols : (symbol * symbol) list; precondition : 'a formula; postcondition: 'a formula}
  type poly_cases = Increment of QQ.t | Reset of QQ.t | Infinite | Unknown_Err | No_Point

  let equal s1 s2 = failwith "not here yet"
  let widen s1 s2 = failwith "not here yet"
  let join s1 s2 = failwith "not here yet"

  
  
  let show vassums =
    let srk = vassums.srk in
    let single_vas_string (vsum : vas_sum) =
      begin match vsum with
        | Bottom (s1, s2) ->
          let str = "(" in
          let str = str ^ (show_symbol srk s1) in
          let str = str ^ ", " in
          let str = str ^ (show_symbol srk s2) in
          str ^ ") : Bottom"
        | Unknown (s1, s2) ->
          let str = "(" in
          let str = str ^ (show_symbol srk s1) in
          let str = str ^ ", " in
          let str = str ^ (show_symbol srk s2) in
          str ^ ") : Unknown"
        | Abstraction v ->
          let str = "(" in
          let str = str ^ (show_symbol srk (fst v.dim)) in
          let str = str ^ ", " in
          let str = str ^ (show_symbol srk (snd v.dim)) in
          let str = str ^ ") : \n Increments: " in
        
          let str = List.fold_left (fun acc ele ->  (acc ^ QQ.show ele ^ ", ")) str (QQSet.elements v.inc) in
          let str = str ^ "\nResets: " in
          List.fold_left (fun acc ele ->  (acc ^ QQ.show ele ^ ", ")) str (QQSet.elements v.res)
      end
    in
    List.fold_left (fun acc vas -> acc ^ (single_vas_string vas) ^ "\n") "" vassums.svvas
 
  let pp formatter vassums =
    let srk = vassums.srk in
    let single_vas_print (vsum : vas_sum) =
      begin match vsum with
        | Bottom (s1, s2) ->
          (*
          Format.pp_print_string formatter "(";
          pp_symbol srk formatter s1;
          Format.pp_print_string formatter ", ";
          pp_symbol srk formatter s2;
          Format.pp_print_string formatter ") : Bottom";
          Format.pp_print_newline formatter ()*)
          Format.fprintf formatter "(%a, %a) : Bottom@\n" (pp_symbol srk) s1 (pp_symbol srk) s2;
        | Unknown (s1, s2) ->
          Format.pp_print_string formatter "(";
          pp_symbol srk formatter s1;
          Format.pp_print_string formatter ", ";
          pp_symbol srk formatter s2;
          Format.pp_print_string formatter ") : Unknown";
          Format.pp_print_newline formatter ()
        | Abstraction v ->
          Format.pp_print_string formatter "(";
          pp_symbol srk formatter (fst v.dim);
          Format.pp_print_string formatter ", ";
          pp_symbol srk formatter (snd v.dim);
          Format.pp_print_string formatter ": ";
          Format.pp_print_newline formatter ();
          Format.pp_print_string formatter "Increments: ";
          List.iter (fun a -> QQ.pp formatter a; Format.pp_print_string formatter ", ") (QQSet.elements v.inc);
          Format.pp_print_newline formatter ();
          Format.pp_print_string formatter "Resets: ";
          List.iter (fun a -> QQ.pp formatter a; Format.pp_print_string formatter ", ") (QQSet.elements v.res);
          Format.pp_print_newline formatter ();
      end
    in
    List.iter (fun a -> single_vas_print a) vassums.svvas
 
  let show vassums = SrkUtil.mk_show pp vassums

  let tr_symbols vassums = vassums.symbols

  let closureX (plus : bool) vassums =
    let srk = vassums.srk in
    let single_vas_closure (vsum : vas_sum) =
      begin match vsum with
        | Bottom (s1, s2) -> mk_true srk
        | Unknown (s1, s2) -> mk_true srk
        | Abstraction v ->
          let incs = v.inc in
          let ress = v.res in
          let d1 = fst v.dim in
          let d2 = snd v.dim in
          let rec compute_inc_plusses incs newsymbs terml  =
            begin match incs with
              | [] -> (newsymbs, terml)
              | hd :: tl -> 
                let new_symb = mk_symbol srk `TyInt in
                let this_mul = mk_mul srk [(mk_const srk new_symb); (mk_real srk hd)] in
                compute_inc_plusses tl (new_symb :: newsymbs) (mk_add srk [this_mul; terml])
            end
          in
          let (syms, plusses) = compute_inc_plusses (QQSet.elements incs) [] (mk_real srk QQ.zero) in
          let rec compute_res_ors ress terml =
            begin match ress with
              | [] -> terml
              | hd :: tl -> compute_res_ors tl (mk_or srk
                                                 [(mk_eq srk (mk_const srk d2)
                                                    (mk_add srk [(mk_real srk hd);
                                                                 plusses])); terml])
            end
          in
          let base_resets = compute_res_ors (QQSet.elements ress)  (mk_false srk) in
          let base_form = 
             if plus then (
               if (List.length syms > 0) then (
                 mk_or srk [base_resets; (mk_and srk [(mk_eq srk (mk_const srk d2) (mk_add srk [(mk_const srk d1); plusses]));
                                                      mk_leq srk (mk_real srk (QQ.of_int 1)) (mk_add srk (List.map (fun var -> mk_const srk var) syms))])])
               else base_resets)
             else mk_or srk [base_resets; (mk_and srk [(mk_eq srk (mk_const srk d2) (mk_add srk [(mk_const srk d1); plusses]))])] in
 
          let base_form_nats = mk_and srk [base_form; List.fold_left (fun form var -> mk_and srk [form; (mk_leq srk (mk_real srk QQ.zero) (mk_const srk var))]) (mk_true srk) syms] in
                   (*let k_largerx = mk_leq srk (mk_real srk (QQ.of_int x)) (mk_add srk (List.map (fun var -> mk_const srk var) syms)) in
          (*List.fold_left (fun form var -> mk_exists_const srk var form) (mk_and srk [base_form_nats; k_largerx]) syms*)
          mk_and srk [base_form_nats; k_largerx]*)
          base_form_nats
      end
    in
    let prepost = if plus then mk_and srk [vassums.precondition; vassums.postcondition] else mk_true srk in
    mk_and srk [prepost; List.fold_left (fun form vas -> mk_and srk [form; (single_vas_closure vas)]) (mk_true srk) vassums.svvas]



  let closure_plus vassums = closureX true vassums

  let closure vassums = closureX false vassums

  let abstract ?(exists=fun x -> true) (srk : 'a context) (symbols : (symbol * symbol) list) (body : 'a formula)  =
    let polyhedron_analysis (formula : 'a formula) (dim1 : symbol) (dim2 : symbol) =
      begin match get_model srk formula with
        | `Unsat -> No_Point
        | `Unknown -> Unknown_Err
       | `Sat interpret ->
         let d1p1 = real interpret dim1  in
          let d2p1 = real interpret dim2 in
          let no_reset_cond = mk_and srk [formula; (mk_not srk (mk_eq srk (mk_const srk dim2) (mk_real srk d2p1)))] in
          begin match get_model srk no_reset_cond with
            | `Unsat -> Reset d2p1
            | `Unknown -> Unknown_Err
            | `Sat interpret ->
              let d1p2 = real interpret dim1 in
              let d2p2 = real interpret dim2 in
              let p1s = QQ.sub d2p1 d1p1 in
              let p2s = QQ.sub d2p2 d1p2 in
              begin match (QQ.equal p1s p2s) with
                | true ->
                  let no_inc_cond = mk_and srk [formula; (mk_not srk 
                                                            (mk_eq srk (mk_sub srk 
                                                                             (mk_const srk dim2)
                                                                             (mk_const srk dim1))
                                                               (mk_real srk p2s)))] in
                  begin match get_model srk no_inc_cond with
                    | `Unsat -> Increment p2s
                    | `Unknown -> Unknown_Err
                    | `Sat interpret -> Infinite
                  end
                | false -> Infinite
              end 
          end
      end
    in 

    let rec pathways_info (form_init : 'a formula) (form_new : 'a formula) dim1 dim2 ress incs  =
      begin match get_model srk form_new with
        | `Unsat -> Abstraction {dim = (dim1, dim2); res = (QQSet.of_list ress); inc = (QQSet.of_list incs)}
        | `Unknown -> Unknown (dim1, dim2)
        | `Sat interpret ->
          begin match select_implicant interpret (rewrite srk ~down:(nnf_rewriter srk) form_init) with
            | None -> Abstraction {dim = (dim1, dim2); res = (QQSet.of_list ress); inc = (QQSet.of_list incs)}
            | Some forms ->
              let combined_formula = mk_and srk forms in
              begin match polyhedron_analysis combined_formula dim1 dim2 with
                | No_Point -> assert false
                | Infinite -> Bottom (dim1, dim2)
                | Unknown_Err -> Unknown (dim1, dim2)
                | Increment i -> pathways_info form_init (mk_and srk [form_new; (mk_not srk (mk_and srk forms))]) dim1 dim2 ress (i :: incs)
                | Reset r -> pathways_info form_init (mk_and srk [form_new; (mk_not srk (mk_and srk forms))]) dim1 dim2 (r :: ress) incs
              end
          end
      end 
    in
    let rec multi_sv_vas symbols =
      begin match symbols with
        | [] -> []
        | (a, b) :: tl -> (pathways_info body body a b [] []) :: (multi_sv_vas tl)
      end
    in

    let manager = Polka.manager_alloc_strict () in
    let existsf pick =  (fun (x : symbol) -> if exists x then List.mem x (List.fold_left (fun acc symb -> (pick symb) :: acc) [] symbols) else false) in
    let pre = SrkApron.formula_of_property (Abstract.abstract ~exists:(existsf fst) srk manager body) in
    let post = SrkApron.formula_of_property (Abstract.abstract ~exists:(existsf snd) srk manager body) in
 
    {srk = srk; svvas = multi_sv_vas symbols; symbols = symbols; precondition = pre; postcondition = post}
  


  (*let widen iter iter' =
    let body = Wedge.widen (wedge_of_iter iter) (wedge_of_iter iter') in
    assert(iter.symbols = iter'.symbols);
    abstract_iter_wedge iter.srk body iter.symbols

  let join iter iter' =
    let body =
      Wedge.join (wedge_of_iter iter) (wedge_of_iter iter')
    in
    assert(iter.symbols = iter'.symbols);
    abstract_iter_wedge iter.srk body iter.symbols*)
end


module Mdvas  = struct
  include Interpretation
  include Smt
  module QQSet = Set.Make(QQ)
  include Mdvas

end

