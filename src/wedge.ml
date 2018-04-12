open Syntax
open BatPervasives

module V = Linear.QQVector
module Monomial = Polynomial.Monomial
module P = Polynomial.Mvp
module Scalar = Apron.Scalar
module Coeff = Apron.Coeff
module Abstract0 = Apron.Abstract0
module Linexpr0 = Apron.Linexpr0
module Lincons0 = Apron.Lincons0
module Dim = Apron.Dim

module CS = CoordinateSystem
module A = BatDynArray

module IntSet = SrkUtil.Int.Set

include Log.Make(struct let name = "srk.wedge" end)

let qq_of_scalar = function
  | Scalar.Float k -> QQ.of_float k
  | Scalar.Mpqf k  -> k
  | Scalar.Mpfrf k -> Mpfrf.to_mpqf k

let qq_of_coeff = function
  | Coeff.Scalar s -> Some (qq_of_scalar s)
  | Coeff.Interval _ -> None

let qq_of_coeff_exn = function
  | Coeff.Scalar s -> qq_of_scalar s
  | Coeff.Interval _ -> invalid_arg "qq_of_coeff_exn: argument must be a scalar"

let coeff_of_qq = Coeff.s_of_mpqf

let scalar_zero = Coeff.s_of_int 0
let scalar_one = Coeff.s_of_int 1

let mk_log = Nonlinear.mk_log
let mk_pow = Nonlinear.mk_pow

let vec_of_poly = P.vec_of ~const:CS.const_id
let poly_of_vec = P.of_vec ~const:CS.const_id

let get_manager =
  let manager = ref None in
  fun () ->
    match !manager with
    | Some man -> man
    | None ->
      let man = Polka.manager_alloc_strict () in
      manager := Some man;
      man

(* Associate coordinates with apron dimensions.  Wedges may share coordinate
    systems, but should *not* share environments -- if the coordinate system
    of a wedge is updated, the wedge is brought back in sync using its
    environment (see update_env). *)
type env = { int_dim : int A.t;
             real_dim : int A.t }

let copy_env env =
  { int_dim = A.copy env.int_dim;
    real_dim = A.copy env.real_dim }

type 'a t =
  { srk : 'a context;
    cs : 'a CS.t;
    env : env;
    mutable abstract : (Polka.strict Polka.t) Abstract0.t }

let dim_of_id cs env id =
  let intd = A.length env.int_dim in
  match CS.type_of_id cs id with
  | `TyInt -> SrkUtil.search id env.int_dim
  | `TyReal -> intd + (SrkUtil.search id env.real_dim)

let id_of_dim env dim =
  let intd = A.length env.int_dim in
  try
    if dim >= intd then
      A.get env.real_dim (dim - intd)
    else
      A.get env.int_dim dim
  with BatDynArray.Invalid_arg _ ->
    invalid_arg "Env.id_of_dim: out of bounds"

let vec_of_linexpr env linexpr =
  let vec = ref V.zero in
  Linexpr0.iter (fun coeff dim ->
      match qq_of_coeff coeff with
      | Some qq when QQ.equal QQ.zero qq -> ()
      | Some qq ->
        vec := V.add_term qq (id_of_dim env dim) (!vec)
      | None -> assert false)
    linexpr;
  match qq_of_coeff (Linexpr0.get_cst linexpr) with
  | Some qq -> V.add_term qq CS.const_id (!vec)
  | None -> assert false

let linexpr_of_vec cs env vec =
  let mk (coeff, id) = (coeff_of_qq coeff, dim_of_id cs env id) in
  let (const_coeff, rest) = V.pivot CS.const_id vec in
  Linexpr0.of_list None
    (BatList.of_enum (BatEnum.map mk (V.enum rest)))
    (Some (coeff_of_qq const_coeff))

let atom_of_lincons wedge lincons =
  let open Lincons0 in
  let term =
    CS.term_of_vec wedge.cs (vec_of_linexpr wedge.env lincons.linexpr0)
  in
  let zero = mk_real wedge.srk QQ.zero in
  match lincons.typ with
  | EQ -> mk_eq wedge.srk term zero
  | SUPEQ -> mk_leq wedge.srk zero term
  | SUP -> mk_lt wedge.srk zero term
  | DISEQ | EQMOD _ -> assert false

let pp formatter wedge =
  Abstract0.print
    (fun dim ->
       SrkUtil.mk_show
         (Term.pp wedge.srk)
         (CS.term_of_coordinate wedge.cs (id_of_dim wedge.env dim)))
    formatter
    wedge.abstract

let show wedge = SrkUtil.mk_show pp wedge

let env_consistent wedge =
  CS.dim wedge.cs = (A.length wedge.env.int_dim) + (A.length wedge.env.real_dim)

(* Should be called when new terms are registered in the environment attached
   to a wedge *)
let update_env wedge =
  let int_dim = A.length wedge.env.int_dim in
  let real_dim = A.length wedge.env.real_dim in
  if int_dim + real_dim < CS.dim wedge.cs then begin
    let added_int = ref 0 in
    let added_real = ref 0 in
    for id = int_dim + real_dim to CS.dim wedge.cs - 1 do
      match CS.type_of_id wedge.cs id with
      | `TyInt  -> (incr added_int; A.add wedge.env.int_dim id)
      | `TyReal -> (incr added_real; A.add wedge.env.real_dim id)
    done;
    let added =
      Array.init (!added_int + !added_real) (fun i ->
          if i < !added_int then
            int_dim
          else
            int_dim + real_dim)
    in
    logf ~level:`trace "update env: adding %d integer and %d real dimension(s)"
      (!added_int)
      (!added_real);
    let abstract =
      Abstract0.add_dimensions
        (get_manager ())
        wedge.abstract
        { Dim.dim = added;
          Dim.intdim = !added_int;
          Dim.realdim = !added_real }
        false
    in
    wedge.abstract <- abstract
  end

let mk_empty_env () = { int_dim = A.create (); real_dim = A.create () }

let mk_env cs =
  let env = mk_empty_env () in
  for id = 0 to CS.dim cs - 1 do
    match CS.type_of_id cs id with
    | `TyInt  -> A.add env.int_dim id
    | `TyReal -> A.add env.real_dim id
  done;
  env

let top context =
  { srk = context;
    cs = CS.mk_empty context;
    abstract = Abstract0.top (get_manager ()) 0 0;
    env = mk_empty_env () }

let is_top wedge = Abstract0.is_top (get_manager ()) wedge.abstract

let bottom context =
  { srk = context;
    cs = CS.mk_empty context;
    abstract = Abstract0.bottom (get_manager ()) 0 0;
    env = mk_empty_env () }

let is_bottom wedge = Abstract0.is_bottom (get_manager ()) wedge.abstract

let to_atoms wedge =
  BatArray.enum (Abstract0.to_lincons_array (get_manager ()) wedge.abstract)
  /@ (atom_of_lincons wedge)
  |> BatList.of_enum

let to_formula wedge = mk_and wedge.srk (to_atoms wedge)

let lincons_of_atom srk cs env atom =
  let vec_of_term = CS.vec_of_term cs in
  let linexpr_of_vec = linexpr_of_vec cs env in
  match Interpretation.destruct_atom srk atom with
  | `Comparison (`Lt, x, y) ->
    Lincons0.make
      (linexpr_of_vec
         (V.add (vec_of_term y) (V.negate (vec_of_term x))))
      Lincons0.SUP
  | `Comparison (`Leq, x, y) ->
    Lincons0.make
      (linexpr_of_vec
         (V.add (vec_of_term y) (V.negate (vec_of_term x))))
      Lincons0.SUPEQ
  | `Comparison (`Eq, x, y) ->
    Lincons0.make
      (linexpr_of_vec
         (V.add (vec_of_term y) (V.negate (vec_of_term x))))
      Lincons0.EQ
  | `Literal (_, _) -> assert false

let meet_atoms wedge atoms =
  (* Ensure that the coordinate system admits each atom *)
  atoms |> List.iter (fun atom ->
      match Interpretation.destruct_atom wedge.srk atom with
      | `Comparison (_, x, y) ->
        CS.admit_term wedge.cs x;
        CS.admit_term wedge.cs y
      | `Literal (_, _) -> assert false);
  update_env wedge;
  let abstract =
    atoms
    |> List.map (lincons_of_atom wedge.srk wedge.cs wedge.env)
    |> Array.of_list
    |> Abstract0.meet_lincons_array (get_manager ()) wedge.abstract
  in
  wedge.abstract <- abstract

let bound_vec wedge vec =
  Abstract0.bound_linexpr
    (get_manager ())
    wedge.abstract
    (linexpr_of_vec wedge.cs wedge.env vec)
  |> Interval.of_apron

let bound_coordinate wedge coordinate =
    bound_vec wedge (V.of_term QQ.one coordinate)

let bound_polynomial wedge polynomial =
  let (t, p) = P.split_linear ~const:CS.const_id polynomial in
  BatEnum.fold (fun ivl (coeff, monomial) ->
      let monomial_ivl = (* bound coeff*monomial *)
        BatEnum.fold (fun ivl (dim, power) ->
            Interval.mul
              ivl
              (Interval.exp_const (bound_coordinate wedge dim) power))
          (Interval.const coeff)
          (Monomial.enum monomial)
      in
      Interval.add ivl monomial_ivl)
    (bound_vec wedge t)
    (P.enum polynomial)

(* Test whether wedge |= x = y *)
let sat_vec_equation wedge x y =
  let eq_constraint =
    Lincons0.make
      (linexpr_of_vec wedge.cs wedge.env (V.add x (V.negate y)))
      Lincons0.EQ
  in
  Abstract0.sat_lincons (get_manager ()) wedge.abstract eq_constraint

let affine_hull wedge =
  let open Lincons0 in
  BatArray.enum (Abstract0.to_lincons_array (get_manager ()) wedge.abstract)
  |> BatEnum.filter_map (fun lcons ->
      match lcons.typ with
      | EQ -> Some (vec_of_linexpr wedge.env lcons.linexpr0)
      | _ -> None)
  |> BatList.of_enum

let polynomial_cone wedge =
  let open Lincons0 in
  BatArray.enum (Abstract0.to_lincons_array (get_manager ()) wedge.abstract)
  |> BatEnum.filter_map (fun lcons ->
      match lcons.typ with
      | SUPEQ | SUP -> Some (poly_of_vec (vec_of_linexpr wedge.env lcons.linexpr0))
      | _ -> None)
  |> BatList.of_enum

let vanishing_ideal wedge =
  let open Lincons0 in
  let ideal = ref [] in
  let add p = ideal := p::(!ideal) in
  Abstract0.to_lincons_array (get_manager ()) wedge.abstract
  |> Array.iter (fun lcons ->
      match lcons.typ with
      | EQ ->
        let vec = vec_of_linexpr wedge.env lcons.linexpr0 in
        add (CS.polynomial_of_vec wedge.cs vec)
      | _ -> ());
  for id = 0 to CS.dim wedge.cs - 1 do
    match CS.destruct_coordinate wedge.cs id with
    | `Inv x ->
      let interval = bound_vec wedge x in
      if not (Interval.elem QQ.zero interval) then
        add (P.sub (P.mul (poly_of_vec x) (P.of_dim id)) (P.scalar QQ.one))
    | _ -> ()
  done;
  !ideal

let coordinate_ideal ?integrity:(integrity=(fun _ -> ())) wedge =
  let srk = wedge.srk in
  let cs = wedge.cs in
  let zero = mk_real srk QQ.zero in
  let polyhedron_ideal =
    List.map poly_of_vec (affine_hull wedge)
  in
  let coordinate_ideal =
    BatEnum.filter_map (fun id ->
        match CS.destruct_coordinate wedge.cs id with
        | `Mul (x, y) ->
          let p =
            P.sub
              (P.of_dim id)
              (P.mul (poly_of_vec x) (poly_of_vec y))
          in
          integrity (mk_eq srk (CS.term_of_polynomial cs p) zero);
          Some p
        | `Inv x ->
          let interval = bound_vec wedge x in
          if Interval.elem QQ.zero interval then
            None
          else begin
            let p =
              P.sub (P.mul (poly_of_vec x) (P.of_dim id)) (P.scalar QQ.one)
            in
            integrity (mk_or srk [mk_eq srk (CS.term_of_vec cs x) zero;
                                  mk_eq srk (CS.term_of_polynomial cs p) zero]);
            Some p
          end
        | _ -> None)
      (0 -- (CS.dim cs - 1))
    |> BatList.of_enum
  in
  polyhedron_ideal@coordinate_ideal

(* Equational saturation.  A polyhedron P is equationally saturated if every
   degree-1 polynomial in the ideal of polynomials vanishing on P + the
   coordinate ideal vanishes on P.  This procedure computes the greatest
   equationally saturated polyhedron contained in the underlying wedge of the
   polyhedron.  *)
let equational_saturation ?integrity:(integrity=(fun _ -> ())) wedge =
  let cs = wedge.cs in
  let srk = wedge.srk in
  let zero = mk_real srk QQ.zero in

  Nonlinear.ensure_symbols wedge.srk;
  assert (env_consistent wedge);

  let saturated = ref false in

  (* Rewrite maintains a Grobner basis for the coordinate ideal + the ideal of
     polynomials vanishing on the underlying polyhedron of the wedge *)
  let rewrite =
    let ideal = coordinate_ideal ~integrity wedge in
    ref (Polynomial.Rewrite.mk_rewrite Monomial.degrevlex ideal
         |> Polynomial.Rewrite.grobner_basis)
  in
  let pp_dim formatter i =
    Term.pp srk formatter (CS.term_of_coordinate wedge.cs i)
  in
  logf "Rewrite: @[<v 0>%a@]" (Polynomial.Rewrite.pp pp_dim) (!rewrite);

  (* Hashtable mapping canonical forms of nonlinear terms to their
     representative terms. *)
  let canonical = Expr.HT.create 991 in

  let provenance_formula ps =
    List.map (fun p -> mk_eq srk (CS.term_of_polynomial cs p) zero) ps
    |> mk_and srk
  in

  let add_bound precondition bound =
    logf ~level:`trace "Integrity: %a => %a"
      (Formula.pp srk) precondition
      (Formula.pp srk) bound;
    integrity (mk_or srk [mk_not srk precondition; bound]);
    meet_atoms wedge [bound]
  in

  let reduce_vec vec =
    let (p, provenance) =
      Polynomial.Rewrite.preduce (!rewrite) (poly_of_vec vec)
    in
    let p_term = CS.term_of_polynomial wedge.cs p in
    let term = CS.term_of_vec wedge.cs vec in
    let integrity =
      if Term.equal p_term term then
        mk_true srk
      else
        mk_if srk
          (provenance_formula provenance)
          (mk_eq srk (CS.term_of_vec wedge.cs vec) p_term)
    in
    (p_term, integrity)
  in

  while not !saturated do
    saturated := true;
    for id = 0 to CS.dim wedge.cs - 1 do
      let term = CS.term_of_coordinate wedge.cs id in
      let (reduced_id, provenance) =
        let (poly, provenance) =
          Polynomial.Rewrite.preduce (!rewrite) (P.of_dim id)
        in
        match vec_of_poly poly with
        | Some p -> (p, provenance_formula provenance)
        | None ->
          (* Reducing a linear polynomial must result in another linear
             polynomial *)
          assert false
      in
      let reduced_term = CS.term_of_vec wedge.cs reduced_id in
      if not (Term.equal term reduced_term) then begin
        add_bound provenance (mk_eq srk term reduced_term)
      end;

      (* congruence closure *)
      let add_canonical reduced provenance =
        (* Add [reduced->term] to the canonical map.  Or if there's already a
           mapping [reduced->rep], add the equation rep=term *)
        if Expr.HT.mem canonical reduced then begin
          logf ~level:`trace "Integrity: %a" (Formula.pp srk) provenance;
          integrity provenance;
          meet_atoms wedge [mk_eq srk term (Expr.HT.find canonical reduced)]
        end else
          Expr.HT.add canonical reduced term
      in
      begin match CS.destruct_coordinate wedge.cs id with
        | `App (_, []) | `Mul (_, _) -> ()
        | `App (func, args) ->
          let (args, provenance) =
            List.fold_right (fun arg (args, provenance) ->
                let (arg',provenance') = reduce_vec arg in
                (arg'::args, provenance'::provenance))
              args
              ([], [])
          in
          add_canonical
            (mk_app srk func args)
            (mk_and srk provenance)
        | `Inv t ->
          let (t', provenance) = reduce_vec t in
          add_canonical (mk_div srk (mk_real srk QQ.one) t') provenance
        | `Mod (num, den) ->
          let (num', nprov) = reduce_vec num in
          let (den', dprov) = reduce_vec den in
          add_canonical (mk_mod srk num' den') provenance
        | `Floor t ->
          let (t', provenance) = reduce_vec t in
          add_canonical (mk_floor srk t') provenance
      end;
    done;
    (* Check for new polynomials vanishing on the underlying polyhedron *)
    affine_hull wedge |> List.iter (fun vec ->
        let reduced =
          Polynomial.Rewrite.reduce (!rewrite) (poly_of_vec vec)
        in
        if not (P.equal P.zero reduced) then begin
          saturated := false;
          rewrite := Polynomial.Rewrite.add_saturate (!rewrite) reduced;
        end);
  done;
  !rewrite

(* Compute bounds for synthetic dimensions using the bounds of their
   operands *)
let strengthen_intervals integrity wedge =
  let cs = wedge.cs in
  let srk = wedge.srk in
  let zero = mk_real srk QQ.zero in
  let log = get_named_symbol srk "log" in
  let add_bound precondition bound =
    logf ~level:`trace "Integrity: %a => %a"
      (Formula.pp srk) precondition
      (Formula.pp srk) bound;
    integrity (mk_or srk [mk_not srk precondition; bound]);
    meet_atoms wedge [bound]
  in

  for id = 0 to CS.dim wedge.cs - 1 do
    let term = CS.term_of_coordinate wedge.cs id in
    match CS.destruct_coordinate wedge.cs id with
    | `Mul (x, y) ->
      let go (x,x_ivl,x_term) (y,y_ivl,y_term) =
        if Interval.is_nonnegative y_ivl then
          begin
            let y_nonnegative = mk_leq srk zero y_term in
            (match Interval.lower x_ivl with
             | Some lo ->
               add_bound
                 (mk_and srk [y_nonnegative; mk_leq srk (mk_real srk lo) x_term])
                 (mk_leq srk (CS.term_of_vec cs (V.scalar_mul lo y)) term)
             | None -> ());
            (match Interval.upper x_ivl with
             | Some hi ->
               add_bound
                 (mk_and srk [y_nonnegative; mk_leq srk x_term (mk_real srk hi)])
                 (mk_leq srk term (CS.term_of_vec cs (V.scalar_mul hi y)))

             | None -> ())
          end
        else if Interval.is_nonpositive y_ivl then
          begin
            let y_nonpositive = mk_leq srk y_term zero in
            (match Interval.lower x_ivl with
             | Some lo ->
               add_bound
                 (mk_and srk [y_nonpositive; mk_leq srk (mk_real srk lo) x_term])
                 (mk_leq srk term (CS.term_of_vec cs (V.scalar_mul lo y)));
             | None -> ());
            (match Interval.upper x_ivl with
             | Some hi ->
               add_bound
                 (mk_and srk [y_nonpositive; mk_leq srk x_term (mk_real srk hi)])
                 (mk_leq srk (CS.term_of_vec cs (V.scalar_mul hi y)) term);
             | None -> ())
          end
        else
          ()
      in

      let x_ivl = bound_vec wedge x in
      let y_ivl = bound_vec wedge y in
      let x_term = CS.term_of_vec cs x in
      let y_term = CS.term_of_vec cs y in

      go (x,x_ivl,x_term) (y,y_ivl,y_term);
      go (y,y_ivl,y_term) (x,x_ivl,x_term);

      let mul_ivl = Interval.mul x_ivl y_ivl in
      let mk_ivl x interval =
        let lower =
          match Interval.lower interval with
          | Some lo -> mk_leq srk (mk_real srk lo) x
          | None -> mk_true srk
        in
        let upper =
          match Interval.upper interval with
          | Some hi -> mk_leq srk x (mk_real srk hi)
          | None -> mk_true srk
        in
        mk_and srk [lower; upper]
      in
      let precondition =
        mk_and srk [mk_ivl x_term x_ivl; mk_ivl y_term y_ivl]
      in
      (match Interval.lower mul_ivl with
       | Some lo -> add_bound precondition (mk_leq srk (mk_real srk lo) term)
       | None -> ());
      (match Interval.upper mul_ivl with
       | Some hi -> add_bound precondition (mk_leq srk term (mk_real srk hi))
       | None -> ())

    | `Floor x ->
      let x_term = CS.term_of_vec cs x in
      let _true = mk_true srk in
      add_bound _true (mk_leq srk term x_term);
      add_bound _true (mk_lt srk
                         (mk_add srk [x_term; mk_real srk (QQ.of_int (-1))])
                         term)

    | `Inv x ->
      (* TODO: preconditions can be weakened *)
      let x_ivl = bound_vec wedge x in
      let x_term = CS.term_of_vec cs x in
      let precondition =
        let lower =
          match Interval.lower x_ivl with
          | Some lo -> [mk_leq srk (mk_real srk lo) x_term]
          | None -> []
        in
        let upper =
          match Interval.upper x_ivl with
          | Some hi -> [mk_leq srk x_term (mk_real srk hi)]
          | None -> []
        in
        mk_and srk (lower@upper)
      in
      let inv_ivl = Interval.div (Interval.const QQ.one) x_ivl in
      begin match Interval.lower inv_ivl with
        | Some lo -> add_bound precondition (mk_leq srk (mk_real srk lo) term)
        | _ -> ()
      end;
      begin match Interval.upper inv_ivl with
        | Some hi -> add_bound precondition (mk_leq srk term (mk_real srk hi))
        | _ -> ()
      end

    | `App (func, [base; exp]) when func = log ->
      let base_ivl = bound_vec wedge base in
      let exp_ivl = bound_vec wedge exp in

      let mk_interval t ivl =
        let lo = match Interval.lower ivl with
          | Some lo -> mk_leq srk (mk_real srk lo) t
          | None -> mk_true srk
        in
        let hi = match Interval.upper ivl with
          | Some hi -> mk_leq srk t (mk_real srk hi)
          | None -> mk_true srk
        in
        (lo, hi)
      in
      let precondition =
        let (lo,hi) = mk_interval (CS.term_of_vec cs base) base_ivl in
        let (lo',hi') = mk_interval (CS.term_of_vec cs exp) exp_ivl in
        mk_and srk [lo;hi;lo';hi']
      in
      let (lo,hi) = mk_interval term (Interval.log base_ivl exp_ivl) in
      add_bound precondition lo;
      add_bound precondition hi

    | `Mod (x, y) ->
      let y_ivl = bound_vec wedge y in
      let zero = mk_real srk QQ.zero in
      add_bound (mk_true srk) (mk_leq srk zero term);
      if Interval.is_positive y_ivl then
        let y_term = CS.term_of_vec cs y in
        add_bound (mk_lt srk zero y_term) (mk_lt srk term y_term)
      else if Interval.is_negative y_ivl then
        let y_term = CS.term_of_vec cs y in
        add_bound (mk_lt srk y_term zero) (mk_lt srk term (mk_neg srk y_term))
      else
        ()

    | `App (func, args) -> ()
  done

let strengthen_products integrity rewrite wedge =
  let cs = wedge.cs in
  let srk = wedge.srk in
  let zero = mk_real srk QQ.zero in
  let mk_geqz p = (* p >= 0 *)
    mk_leq srk (mk_neg srk (CS.term_of_polynomial wedge.cs p)) zero
  in
  let provenance_formula ps =
    List.map (fun p -> mk_eq srk (CS.term_of_polynomial cs p) zero) ps
    |> mk_and srk
  in
  let add_bound precondition bound =
    logf ~level:`trace "Integrity: %a => %a"
      (Formula.pp srk) precondition
      (Formula.pp srk) bound;
    integrity (mk_or srk [mk_not srk precondition; bound]);
    meet_atoms wedge [bound]
  in
  let rec add_products = function
    | [] -> ()
    | (p::cone) ->
      cone |> List.iter (fun q ->
          let (r, provenance) =
            Polynomial.Rewrite.preduce rewrite (P.mul p q)
          in
          match vec_of_poly r with
          | Some r ->
            let precondition =
              mk_and srk [provenance_formula provenance;
                          mk_geqz p;
                          mk_geqz q]
            in
            let r_geqz = (* r >= 0 *)
              mk_leq srk (CS.term_of_vec wedge.cs (V.negate r)) zero
            in
            add_bound precondition r_geqz
          | None -> ());
      add_products cone
  in
  add_products (polynomial_cone wedge)

(* Tighten integral dimensions.  No need for integrity constraints -- the
   added constraints are valid in all linear models. *)
let strengthen_integral wedge =
  let srk = wedge.srk in
  for id = 0 to CS.dim wedge.cs - 1 do
    match CS.type_of_id wedge.cs id with
    | `TyInt ->
      let term = CS.term_of_coordinate wedge.cs id in
      let interval = bound_coordinate wedge id in
      begin
        match Interval.lower interval with
        | Some lo when QQ.to_zz lo = None ->
          meet_atoms wedge [mk_leq srk (mk_real srk lo) term]
        | _ -> ()
      end;
      begin
        match Interval.upper interval with
        | Some hi when QQ.to_zz hi = None ->
          meet_atoms wedge [mk_leq srk term (mk_real srk hi)]
        | _ -> ()
      end
    | _ -> ()
  done

let strengthen ?integrity:(integrity=(fun _ -> ())) wedge =
  Nonlinear.ensure_symbols wedge.srk;
  assert (env_consistent wedge);
  let cs = wedge.cs in
  let srk = wedge.srk in
  let zero = mk_real srk QQ.zero in
  let log = get_named_symbol srk "log" in
  let pow = get_named_symbol srk "pow" in
  let add_bound precondition bound =
    logf ~level:`trace "Integrity: %a => %a"
      (Formula.pp srk) precondition
      (Formula.pp srk) bound;
    integrity (mk_or srk [mk_not srk precondition; bound]);
    meet_atoms wedge [bound]
  in

  let provenance_formula ps =
    List.map (fun p -> mk_eq srk (CS.term_of_polynomial cs p) zero) ps
    |> mk_and srk
  in

  logf "Before strengthen: %a" pp wedge;

  let rewrite = equational_saturation ~integrity wedge in

  (* pow-log rule *)
  let vec_sign vec =
    let ivl = bound_vec wedge vec in
    if Interval.is_positive ivl then
      `Positive
    else if Interval.is_negative ivl then
      `Negative
    else
      `Unknown
  in
  let vec_leq x y =
    Interval.is_nonpositive (bound_vec wedge (V.add x (V.negate y)))
  in
  for i = 0 to CS.dim wedge.cs - 1 do
    match CS.destruct_coordinate wedge.cs i with
    | `App (func, [b; s]) when func = pow ->
      if vec_sign b = `Positive then begin
        begin
          let ivl = bound_coordinate wedge i in
          let logc_ivl = Interval.log (bound_vec wedge b) ivl in
          match Interval.lower ivl with
          | Some lo when QQ.lt QQ.zero lo ->
            begin match Interval.lower logc_ivl with
              | Some logc ->
                let hypothesis =
                  mk_and srk [mk_leq srk (mk_real srk lo) (CS.term_of_coordinate cs i);
                              mk_lt srk zero (CS.term_of_vec cs b)]
                in
                let conclusion =
                  mk_leq srk (mk_real srk logc) (CS.term_of_vec cs s)
                in
                add_bound hypothesis conclusion
              | None -> ()
            end;
            begin match Interval.upper ivl, Interval.upper logc_ivl with
              | Some hi, Some logc ->
                let hypothesis =
                  mk_and srk [mk_leq srk (CS.term_of_coordinate cs i) (mk_real srk hi);
                              mk_lt srk zero (CS.term_of_vec cs b)]
                in
                let conclusion =
                  mk_leq srk (mk_real srk logc) (CS.term_of_vec cs s)
                in
                add_bound hypothesis conclusion
              | _, _ -> ()
            end
          | _ -> ()
        end;
        for j = 0 to CS.dim wedge.cs - 1 do
          match CS.destruct_coordinate wedge.cs j with
          | `App (func, [b'; t]) when func = log->
            let (base_eq, base_eq_prov) =
              let (reduced, prov) =
                P.sub (poly_of_vec b) (poly_of_vec b')
                |> Polynomial.Rewrite.preduce rewrite
              in
              (P.equal reduced P.zero, prov)
            in
            if base_eq && vec_sign t = `Positive then
              let t_sub_bs_ivl = (* t - b^s >= 0? *)
                V.add_term (QQ.of_int (-1)) i t
                |> bound_vec wedge
              in
              begin
                (* 0 < b && b^s <= t |= s <= log_b(t) *)
                if Interval.is_nonnegative t_sub_bs_ivl then
                  let hypothesis =
                    mk_and srk [mk_lt srk zero (CS.term_of_vec cs b);
                                mk_leq srk
                                  (CS.term_of_coordinate cs i)
                                  (CS.term_of_vec cs t);
                                provenance_formula base_eq_prov]
                  in
                  let conclusion =
                    mk_leq srk (CS.term_of_vec cs s) (CS.term_of_coordinate cs j)
                  in
                  add_bound hypothesis conclusion
              end;
              begin
                (* 0 < t <= b^s |= log_b(t) <= s *)
                if Interval.is_nonpositive t_sub_bs_ivl then
                  let hypothesis =
                    mk_and srk [mk_lt srk zero (CS.term_of_vec cs t);
                                mk_leq srk
                                  (CS.term_of_vec cs t)
                                  (CS.term_of_coordinate cs i);
                                provenance_formula base_eq_prov]
                  in
                  let conclusion =
                    mk_leq srk (CS.term_of_coordinate cs j) (CS.term_of_vec cs s)
                  in
                  add_bound hypothesis conclusion
              end;
              begin
                let p = (* b^s * t *)
                  P.mul
                    (CS.polynomial_of_coordinate cs i)
                    (CS.polynomial_of_coordinate cs j)
                in
                match vec_of_poly (Polynomial.Rewrite.reduce rewrite p) with
                | None -> ()
                | Some vec ->
                  let ivl = bound_vec wedge vec in
                  let p_term = CS.term_of_vec cs vec in
                  let logbc_ivl =
                    Interval.log (bound_vec wedge b) ivl
                  in
                  (* 0 < c <= (b^s)*t && 0 < t && 0 < b^s
                     |= log_b(c) <= log_b(t) + s *)
                  begin match Interval.lower ivl, Interval.lower logbc_ivl with
                    | Some lo, Some logbc when QQ.lt QQ.zero lo ->
                      let hypothesis =
                        mk_and srk [mk_lt srk (mk_real srk lo) p_term;
                                    mk_lt srk zero (CS.term_of_vec cs t);
                                    mk_lt srk zero (CS.term_of_coordinate cs i)]
                      in
                      let conclusion =
                        mk_leq srk
                          (mk_real srk logbc)
                          (mk_add srk [CS.term_of_coordinate cs j;
                                       CS.term_of_vec cs s])
                      in
                      add_bound hypothesis conclusion
                    | _, _ -> ()
                  end;
                  (* 0 < t && 0 < b && (b^s)*t <= c |= log_b(t) + s <= log_b(c) *)
                  begin match Interval.upper ivl, Interval.upper logbc_ivl with
                    | Some hi, Some logbc ->
                      let hypothesis =
                        mk_and srk [mk_lt srk p_term (mk_real srk hi);
                                    mk_lt srk zero (CS.term_of_vec cs t);
                                    mk_lt srk zero (CS.term_of_coordinate cs i)]
                      in
                      let conclusion =
                        mk_leq srk
                          (mk_add srk [CS.term_of_coordinate cs j;
                                       CS.term_of_vec cs s])
                          (mk_real srk logbc)
                      in
                      add_bound hypothesis conclusion
                    | _, _ -> ()
                  end
              end
          | `App (func, [b'; s']) when func = pow ->
            (* 1 <= b <= b' && s <= s' |= b^s <= b'^s' *)
            let one = V.of_term QQ.one CS.const_id in
            begin
              if vec_leq one b && vec_leq b b' && vec_leq s s' then
                let hypothesis =
                  mk_and srk [mk_leq srk (CS.term_of_vec cs b)
                                (CS.term_of_vec cs b');
                              mk_leq srk (CS.term_of_vec cs s)
                                (CS.term_of_vec cs s');
                              mk_leq srk (mk_real srk QQ.one)
                                (CS.term_of_vec cs b)]
                in
                let conclusion =
                  mk_leq srk
                    (CS.term_of_coordinate cs i)
                    (CS.term_of_coordinate cs j)
                in
                add_bound hypothesis conclusion
            end;
            begin
              (* 1 <= b && b <= b' && b^s <= b'^s' |= s <= s' *)
              let ivec = V.of_term QQ.one i in
              let jvec = V.of_term QQ.one j in
              if vec_leq one b && vec_leq b b' && vec_leq ivec jvec then
                let hypothesis =
                  mk_and srk [mk_leq srk (CS.term_of_vec cs b)
                                (CS.term_of_vec cs b');
                              mk_leq srk (CS.term_of_coordinate cs i)
                                (CS.term_of_coordinate cs j);
                              mk_leq srk (mk_real srk QQ.one)
                                (CS.term_of_vec cs b)]
                in
                let conclusion =
                  mk_leq srk (CS.term_of_vec cs s) (CS.term_of_vec cs s')
                in
                add_bound hypothesis conclusion
            end
          | _ -> ()
        done
      end
    | _ -> ()
  done;

  strengthen_intervals integrity wedge;
  strengthen_products integrity rewrite wedge;
  strengthen_integral wedge;

  ignore (equational_saturation ~integrity wedge);
  logf "After strengthen: %a" pp wedge

let of_atoms srk atoms =
  let cs = CS.mk_empty srk in
  let register_terms atom =
    match Interpretation.destruct_atom srk atom with
    | `Comparison (_, x, y) ->
      CS.admit_term cs x;
      CS.admit_term cs y
    | `Literal (_, _) -> assert false
  in
  List.iter register_terms atoms;
  let env = mk_env cs in
  let abstract =
    Abstract0.of_lincons_array
      (get_manager ())
      (A.length env.int_dim)
      (A.length env.real_dim)
      (Array.of_list (List.map (lincons_of_atom srk cs env) atoms))
  in
  let wedge =
    { srk = srk;
      cs = cs;
      env = env;
      abstract = abstract }
  in

  (* Add inverse coordinates for nonzero subterms of multiplicative terms *)
(*
  for id = 0 to CS.dim wedge.cs - 1 do
    match CS.destruct_coordinate wedge.cs id with
    | `Mul (x, y) ->
      if not (Interval.elem QQ.zero (bound_vec wedge x)) then
        CS.admit_cs_term wedge.cs (`Inv x);
      if not (Interval.elem QQ.zero (bound_vec wedge y)) then
        CS.admit_cs_term wedge.cs (`Inv y);
    | _ -> ()
  done;
*)
  update_env wedge;
  wedge

let common_cs wedge wedge' =
  let srk = wedge.srk in
  let cs = CS.mk_empty srk in
  let register_terms atom =
    match Interpretation.destruct_atom srk atom with
    | `Comparison (_, x, y) ->
      CS.admit_term cs x;
      CS.admit_term cs y
    | `Literal (_, _) -> assert false
  in
  let atoms = to_atoms wedge in
  let atoms' = to_atoms wedge' in
  List.iter register_terms atoms;
  List.iter register_terms atoms';
  let env = mk_env cs in
  let env' = mk_env cs in
  let wedge =
    { srk = srk;
      cs = cs;
      env = env;
      abstract =
        Abstract0.of_lincons_array
          (get_manager ())
          (A.length env.int_dim)
          (A.length env.real_dim)
          (Array.of_list (List.map (lincons_of_atom srk cs env) atoms)) }
  in
  let wedge' =
    { srk = srk;
      cs = cs;
      env = env';
      abstract =
        Abstract0.of_lincons_array
          (get_manager ())
          (A.length env.int_dim)
          (A.length env.real_dim)
          (Array.of_list (List.map (lincons_of_atom srk cs env) atoms')) }
  in
  (wedge, wedge')

let join ?integrity:(integrity=(fun _ -> ())) wedge wedge' =
  if is_bottom wedge then wedge'
  else if is_bottom wedge' then wedge
  else
    let (wedge, wedge') = common_cs wedge wedge' in
    strengthen ~integrity wedge;
    update_env wedge';
    strengthen ~integrity wedge';
    update_env wedge; (* strengthening wedge' may add dimensions to the common
                         coordinate system -- add those dimensions to wedge's
                         environment *)
    { srk = wedge.srk;
      cs = wedge.cs;
      env = wedge.env;
      abstract =
        Abstract0.join (get_manager ()) wedge.abstract wedge'.abstract }

let copy wedge =
  { srk = wedge.srk;
    cs = CS.copy wedge.cs;
    env = copy_env wedge.env;
    abstract = wedge.abstract }

let meet wedge wedge' =
  if is_top wedge then copy wedge'
  else if is_top wedge' then copy wedge
  else begin
    let wedge = copy wedge in
    meet_atoms wedge (to_atoms wedge');
    wedge
  end

let join ?integrity:(integrity=(fun _ -> ())) wedge wedge' =
  Log.time "wedge join" (join ~integrity wedge) wedge'

let equal wedge wedge' =
  let srk = wedge.srk in
  let phi = Nonlinear.uninterpret srk (to_formula wedge) in
  let phi' = Nonlinear.uninterpret srk (to_formula wedge') in
  match Smt.is_sat srk (mk_not srk (mk_iff srk phi phi')) with
  | `Sat -> false
  | `Unsat -> true
  | `Unknown -> assert false

(* Remove dimensions from an abstract value so that it has the specified
   number of integer and real dimensions *)
let apron_set_dimensions new_int new_real abstract =
  let open Dim in
  let abstract_dim = Abstract0.dimension (get_manager ()) abstract in
  let remove_int = abstract_dim.intd - new_int in
  let remove_real = abstract_dim.reald - new_real in
  if remove_int > 0 || remove_real > 0 then
    let remove =
      BatEnum.append
        (new_int -- (abstract_dim.intd - 1))
        ((abstract_dim.intd + new_real)
         -- (abstract_dim.intd + abstract_dim.reald - 1))
      |> BatArray.of_enum
    in
    logf ~level:`trace "Remove %d int, %d real: %a" remove_int remove_real
      (SrkUtil.pp_print_enum Format.pp_print_int) (BatArray.enum remove);
    assert (remove_int + remove_real = (Array.length remove));
    Abstract0.remove_dimensions
      (get_manager ())
      abstract
      { dim = remove;
        intdim = remove_int;
        realdim = remove_real }
  else
    abstract

(** Project a set of coordinates out of an abstract value *)
let forget_ids wedge abstract forget =
  let forget_dims =
    Array.of_list (List.map (dim_of_id wedge.cs wedge.env) forget)
  in
  BatArray.sort Pervasives.compare forget_dims;
  Abstract0.forget_array
    (get_manager ())
    abstract
    forget_dims
    false

(* Get a list of symbolic lower and upper bounds for a vector, expressed in
   terms of identifiers that do not belong to forget *)
let symbolic_bounds_vec wedge vec forget =
  assert (env_consistent wedge);

  (* Add one real dimension to store the vector *)
  let vec_dim = CS.dim wedge.cs in
  let abstract =
    Abstract0.add_dimensions
      (get_manager ())
      wedge.abstract
      { Dim.dim = [| vec_dim |];
        Dim.intdim = 0;
        Dim.realdim = 1 }
      false
  in
  (* Store the vector in vec_dim *)
  begin
    let linexpr = linexpr_of_vec wedge.cs wedge.env vec in
    Linexpr0.set_coeff linexpr vec_dim (Coeff.s_of_int (-1));
    Abstract0.meet_lincons_array_with
      (get_manager ())
      abstract
      [| Lincons0.make linexpr Lincons0.EQ |]
  end;
  (* Project undesired identifiers *)
  let abstract = forget_ids wedge abstract forget in

  (* Compute bounds *)
  let lower = ref [] in
  let upper = ref [] in

  Abstract0.to_lincons_array (get_manager ()) abstract
  |> BatArray.iter (fun lincons ->
      let open Lincons0 in
      let a =
        qq_of_coeff_exn (Linexpr0.get_coeff lincons.linexpr0 vec_dim)
      in
      if not (QQ.equal a QQ.zero) then begin
        (* Write lincons.linexpr0 as "vec comp bound" *)
        Linexpr0.set_coeff lincons.linexpr0 vec_dim (coeff_of_qq QQ.zero);
        let bound =
          vec_of_linexpr wedge.env lincons.linexpr0
          |> V.scalar_mul (QQ.negate (QQ.inverse a))
          |> CS.term_of_vec wedge.cs
        in
        match lincons.typ with
        | SUP | SUPEQ ->
          if QQ.lt QQ.zero a then
            lower := bound::(!lower)
          else
            upper := bound::(!upper)
        | EQ ->
          lower := bound::(!lower);
          upper := bound::(!upper)
        | _ -> ()
      end);
  (!lower, !upper)


let exists
    ?integrity:(integrity=(fun _ -> ()))
    ?subterm:(subterm=(fun _ -> true))
    p
    wedge =
  logf "Projection input: %a" pp wedge;
  let wedge = copy wedge in
  let srk = wedge.srk in
  let cs = wedge.cs in
  Nonlinear.ensure_symbols srk;
  let log = get_named_symbol srk "log" in
  let pow = get_named_symbol srk "pow" in

  let keep x = p x || x = log || x = pow in
  let subterm x = keep x && subterm x in
  let safe_coordinates =
    CS.project_ideal cs (coordinate_ideal ~integrity wedge) ~subterm keep
  in
  List.iter (fun (_,_,thm) -> integrity thm) safe_coordinates;

  (* Coordinates that must be projected out *)
  let forget =
    List.fold_left (fun set (i, _, _) ->
        IntSet.remove i set)
      (IntSet.of_enum (0 -- (CS.dim cs - 1)))
      safe_coordinates
  in
  let forget_subterm =
    List.fold_left (fun set (i, _, _) ->
        let t = CS.term_of_coordinate cs i in
        if Symbol.Set.for_all subterm (symbols t) then
          IntSet.remove i set
        else
          set)
      (IntSet.of_enum (0 -- (CS.dim cs - 1)))
      safe_coordinates
  in

  let safe_vector vec = (* to do: rewrite first *)
    V.enum vec
    |> BatEnum.for_all (fun (_, dim) -> not (IntSet.mem dim forget))
  in

  (***************************************************************************
   * Build environment of the projection and a translation into the projected
   * environment.
   ***************************************************************************)
  let new_cs = CS.mk_empty srk in
  let substitution =
    safe_coordinates |> List.map (fun (id,term,_) ->
        let dim = dim_of_id wedge.cs wedge.env id in
        let rewrite_vec = CS.vec_of_term ~admit:true new_cs term in
        (dim, rewrite_vec))
  in
  let new_env = mk_env new_cs in
  let abstract = forget_ids wedge wedge.abstract (IntSet.elements forget) in

  (* Ensure abstract has enough dimensions to be able to interpret the
     substitution.  The substituion is interpreted within an implicit
     ("virtual") environment. *)
  let virtual_int_dim =
    max (CS.int_dim cs) (CS.int_dim new_cs)
  in
  let virtual_dim_of_id id =
    let open Env in
    match CS.type_of_id new_cs id with
    | `TyInt -> SrkUtil.search id new_env.int_dim
    | `TyReal -> virtual_int_dim + (SrkUtil.search id new_env.real_dim)
  in
  let virtual_linexpr_of_vec vec =
    let mk (coeff, id) =
      (coeff_of_qq coeff, virtual_dim_of_id id)
    in
    let (const_coeff, rest) = V.pivot CS.const_id vec in
    Linexpr0.of_list None
      (BatList.of_enum (BatEnum.map mk (V.enum rest)))
      (Some (coeff_of_qq const_coeff))
  in

  let abstract =
    let int_dims = A.length wedge.env.int_dim in
    let real_dims = A.length wedge.env.real_dim in
    let added_int = max 0 ((A.length new_env.int_dim) - int_dims) in
    let added_real = max 0 ((A.length new_env.real_dim) - real_dims) in
    let added =
      BatEnum.append
        ((0 -- (added_int - 1)) /@ (fun _ -> int_dims))
        ((0 -- (added_real - 1)) /@ (fun _ -> int_dims + real_dims))
      |> BatArray.of_enum
    in
    Abstract0.add_dimensions
      (get_manager ())
      abstract
      { Dim.dim = added;
        Dim.intdim = added_int;
        Dim.realdim = added_real }
      false
  in

  logf ~level:`trace "Env (%d): %a"
    (List.length substitution)
    CS.pp new_cs;
  substitution |> List.iter (fun (dim, replacement) ->
      logf ~level:`trace "Replace %a => %a"
        (Term.pp srk) (CS.term_of_coordinate wedge.cs (id_of_dim wedge.env dim))
        (CS.pp_vector new_cs) replacement);

  let abstract =
    Abstract0.substitute_linexpr_array
      (get_manager ())
      abstract
      (BatArray.of_list (List.map fst substitution))
      (BatArray.of_list (List.map (virtual_linexpr_of_vec % snd) substitution))
      None
  in

  (* Remove extra dimensions *)
  let abstract =
    apron_set_dimensions
      (A.length new_env.int_dim)
      (A.length new_env.real_dim)
      abstract
  in
  let result =
    { srk = srk;
      cs = new_cs;
      env = new_env;
      abstract = abstract }
  in

  (***************************************************************************
   * Find new non-linear terms to improve the projection
   ***************************************************************************)
  let add_bound precondition bound =
    logf ~level:`trace "Integrity: %a => %a"
      (Formula.pp srk) precondition
      (Formula.pp srk) bound;
    integrity (mk_if srk precondition bound);
    meet_atoms result [bound]
  in
  (* find a polynomial p such that p*interp(i) = interp(j).  The coordinate j
     is assumed to be non-multiplicative. *)
  let div_coordinate i j =
    assert (i >= 0);
    P.div_monomial
      (CS.polynomial_of_coordinate cs i)
      (Monomial.singleton j 1)
  in
  let gt_one b =
    Interval.is_positive
      (Interval.add (bound_vec wedge b) (Interval.const (QQ.of_int (-1))))
  in

  forget |> IntSet.iter (fun id ->
      let term = CS.term_of_coordinate cs id in
      match CS.destruct_coordinate cs id with

      (* p*b^s + t >= 0 /\ b > 1 /\ p >= 0 && t <= 0
         |= log_b(p) + s >= log_b(t) *)
      (* p*b^s + t >= 0 /\ b > 1 /\ p <= 0 && t >= 0
         |= log_b(p) + s <= log_b(t) *)
      (* s >= t /\ b > 1 |= b^s >= b^t *)
      (* s <= t /\ b > 1 |= b^s <= b^t *)
      | `App (symbol, [b; s])
        when (symbol = pow && safe_vector b && gt_one b) ->

        (* Find inequations of the form p*b^s + t >= 0, where p is a
           polynomial over safe dimensions and t is a linear term over safe
           dimensions *)
        let bs_multiples =
          IntSet.filter (fun j ->
              match div_coordinate j id with
              | Some q ->
                BatEnum.for_all
                  (fun dim -> not (IntSet.mem dim forget_subterm))
                  (P.dimensions q)
              | None -> false)
            forget_subterm
        in
        let b_term = CS.term_of_vec cs b in
        let s_term = CS.term_of_vec cs s in
        (* forget unsafe dimensions that can't be factored as p*b^s *)
        let forget' =
          IntSet.elements forget_subterm
          |> List.filter (fun x -> not (IntSet.mem x bs_multiples))
        in
        forget_ids wedge wedge.abstract forget'
        |> Abstract0.to_lincons_array (get_manager ())
        |> Array.iter (fun lincons ->
            let open Lincons0 in
            let vec = V.negate (vec_of_linexpr wedge.env lincons.linexpr0) in
            (* rewrite vec as p*b^s + t *)
            let (p, t) =
              let (const_coeff, vec) = V.pivot CS.const_id vec in
              BatEnum.fold (fun (p,t) (coeff, dim) ->
                  match div_coordinate dim id with
                  | Some q ->
                    (P.add p (P.scalar_mul coeff q), t)
                  | None ->
                    (p, V.add_term coeff dim t))
                (P.zero, V.of_term const_coeff CS.const_id)
                (V.enum vec)
            in
            let p_ivl = bound_polynomial wedge p in
            let t_ivl = bound_vec wedge t in
            let p_term = CS.term_of_polynomial cs p in
            let t_term = CS.term_of_vec cs t in

            (* integrity constraint needed to prove bounds for p *)
            let p_ivl_integrity =
              let (v,q) = P.split_linear p in
              let constraints =
                BatEnum.fold (fun constraints dim ->
                    let dim_ivl = bound_coordinate wedge dim in
                    let dim_term = CS.term_of_coordinate cs dim in
                    let constraints =
                      match Interval.lower dim_ivl with
                      | Some lo ->
                          (mk_leq srk (mk_real srk lo) dim_term)::constraints
                      | None -> constraints
                    in
                    match Interval.upper dim_ivl with
                    | Some hi ->
                      (mk_leq srk dim_term (mk_real srk hi))::constraints
                    | None -> constraints)
                  []
                  (P.dimensions q)
              in
              let q_ivl =
                let ivl = bound_polynomial wedge q in
                let q_term = CS.term_of_polynomial cs q in
                let q_ivl =
                  match Interval.lower ivl with
                  | Some lo -> [mk_leq srk (mk_real srk lo) q_term]
                  | None -> []
                in
                match Interval.upper ivl with
                | Some hi -> (mk_leq srk q_term (mk_real srk hi))::q_ivl
                | None -> q_ivl
              in
              mk_if srk (mk_and srk constraints) (mk_and srk q_ivl)
            in
            if Interval.is_positive p_ivl && Interval.is_negative t_ivl then
              let hypothesis =
                mk_and srk [atom_of_lincons wedge lincons;
                            mk_lt srk (mk_real srk QQ.one) b_term;
                            mk_lt srk (mk_real srk QQ.zero) p_term;
                            mk_lt srk t_term (mk_real srk QQ.zero)]
              in
              let conclusion =
                mk_leq srk
                  (mk_add srk
                     [mk_log srk b_term p_term;
                      s_term])
                  (mk_log srk b_term (mk_neg srk t_term))
              in
              integrity p_ivl_integrity;
              add_bound hypothesis conclusion
            else if Interval.is_negative p_ivl && Interval.is_positive t_ivl then
              let hypothesis =
                mk_and srk [atom_of_lincons wedge lincons;
                            mk_lt srk (mk_real srk QQ.one) b_term;
                            mk_lt srk p_term (mk_real srk QQ.zero);
                            mk_lt srk (mk_real srk QQ.zero) t_term]
              in
              let conclusion =
                mk_leq srk
                  (mk_log srk b_term t_term)
                  (mk_add srk
                     [mk_log srk b_term (mk_neg srk p_term);
                      s_term])
              in
              integrity p_ivl_integrity;
              add_bound hypothesis conclusion);

        let (lower_t, upper_t) =
          symbolic_bounds_vec wedge
            (CS.vec_of_term cs term)
            (IntSet.elements forget_subterm)
        in
        let (lower, upper) =
          symbolic_bounds_vec wedge s (IntSet.elements forget_subterm)
        in
        lower |> List.iter (fun lo ->
            upper_t |> List.iter (fun hi ->
                let hypothesis =
                  mk_and srk [mk_lt srk (mk_real srk QQ.one) b_term;
                              mk_leq srk lo s_term;
                              mk_leq srk term hi]
                in
                let conclusion = mk_leq srk (mk_pow srk b_term lo) hi in
                add_bound hypothesis conclusion));
        upper |> List.iter (fun hi ->
            lower_t |> List.iter (fun lo ->
                let hypothesis =
                  mk_and srk [mk_lt srk (mk_real srk QQ.one) b_term;
                              mk_leq srk s_term hi;
                              mk_leq srk lo term]
                in
                let conclusion = mk_leq srk lo (mk_pow srk b_term hi) in
                add_bound hypothesis conclusion));

      | `App (symbol, [base; x]) when symbol = log ->
        (* If 1 < base then
             lo <= x <= hi ==> log(base,lo) <= log(base, x) <= log(base,hi) *)
        begin
          match BatList.of_enum (V.enum base) with
          | [(base,base_id)] when base_id = CS.const_id
                               && QQ.lt QQ.one base ->
            let (lower, upper) =
              symbolic_bounds_vec wedge x (IntSet.elements forget_subterm)
            in
            let x_term = CS.term_of_vec cs x in
            let base_term = mk_real srk base in
            lower |> List.iter (fun lo ->
                add_bound
                  (mk_leq srk lo x_term)
                  (mk_leq srk (mk_log srk base_term lo) term));
            upper |> List.iter (fun hi ->
                add_bound
                  (mk_leq srk x_term hi)
                  (mk_leq srk term (mk_log srk base_term hi)))
          | _ -> ()
        end
      | _ -> ());

  logf "Projection result: %a" pp result;
  result

let widen wedge wedge' =
  let srk = wedge.srk in
  let widen_cs = CS.mk_empty srk in
  for id = 0 to (CS.dim wedge.cs) - 1 do
    let term = CS.term_of_coordinate wedge.cs id in
    if CS.admits wedge'.cs term then
      CS.admit_term widen_cs term
  done;
  let widen_env = mk_env widen_cs in

  (* Project onto intersected environment *)
  let project wedge =
    let forget = ref [] in
    let substitution = ref [] in
    for id = 0 to (CS.dim wedge.cs) - 1 do
      let term = CS.term_of_coordinate wedge.cs id in
      let dim = dim_of_id wedge.cs wedge.env id in
      if CS.admits widen_cs term then
        substitution := (dim, CS.vec_of_term widen_cs term)::(!substitution)
      else
        forget := dim::(!forget)
    done;
    let abstract =
      Abstract0.forget_array
        (get_manager ())
        wedge.abstract
        (Array.of_list (List.rev (!forget)))
        false
    in
    let abstract =
      Abstract0.substitute_linexpr_array
        (get_manager ())
        abstract
        (BatArray.of_list (List.map fst (!substitution)))
        (BatArray.of_list
           (List.map (linexpr_of_vec widen_cs widen_env % snd) (!substitution)))
        None
    in
    apron_set_dimensions
      (A.length widen_env.int_dim)
      (A.length widen_env.real_dim)
      abstract
  in
  let abstract = project wedge in
  let abstract' = project wedge' in
  { srk = srk;
    cs = widen_cs;
    env = widen_env;
    abstract = Abstract0.widening (get_manager ()) abstract abstract' }

let widen wedge wedge' =
  if is_top wedge' then top wedge.srk
  else if is_bottom wedge' then wedge
  else widen wedge wedge'

let farkas_equalities wedge =
  let open Lincons0 in
  let constraints =
    BatArray.enum (Abstract0.to_lincons_array (get_manager ()) wedge.abstract)
    |> BatEnum.filter_map (fun lcons ->
        match lcons.typ with
        | EQ -> Some lcons.linexpr0
        | _ -> None)
    |> BatArray.of_enum
  in
  let nb_columns =
    let dim = Abstract0.dimension (get_manager ()) wedge.abstract in
    (* one extra column for the constant *)
    dim.Dim.intd + dim.Dim.reald + 1
  in
  let columns =
    Array.init nb_columns (fun _ -> V.zero)
  in
  for row = 0 to Array.length constraints - 1 do
    constraints.(row) |> Linexpr0.iter (fun coeff col ->
        columns.(col) <- V.add_term (qq_of_coeff_exn coeff) row columns.(col));
    columns.(nb_columns - 1) <- V.add_term
        (qq_of_coeff_exn (Linexpr0.get_cst constraints.(row)))
        row
        columns.(nb_columns - 1)
  done;
  Array.mapi (fun id column ->
      let term =
        if id = (nb_columns - 1) then
          mk_real wedge.srk QQ.one
        else
          CS.term_of_coordinate wedge.cs id
      in
      (term, column))
    columns
  |> Array.to_list

let symbolic_bounds wedge symbol =
  let srk = wedge.srk in
  let term = (mk_const srk symbol) in
  if CS.admits wedge.cs term then
    let vec = CS.vec_of_term wedge.cs term in
    match BatList.of_enum (V.enum vec) with
    | [(coeff, id)] ->
      assert (QQ.equal coeff QQ.one);

      let constraints =
        Abstract0.to_lincons_array (get_manager ()) wedge.abstract
      in
      BatEnum.fold (fun (lower, upper) lincons ->
          let open Lincons0 in
          let vec = vec_of_linexpr wedge.env lincons.linexpr0 in
          let (a, t) = V.pivot id vec in
          if QQ.equal a QQ.zero then
            (lower, upper)
          else
            let bound =
              V.scalar_mul (QQ.negate (QQ.inverse a)) t
              |> CS.term_of_vec wedge.cs
            in
            match lincons.typ with
            | EQ -> (bound::lower, bound::upper)
            | SUP | SUPEQ ->
              if QQ.lt QQ.zero a then
                (bound::lower, upper)
              else
                (lower, bound::upper)
            | _ -> (lower, upper)
        )
        ([], [])
        (BatArray.enum constraints)
    | _ -> assert false
  else
    ([], [])

let is_sat srk phi =
  let phi = eliminate_ite srk phi in
  let phi = SrkSimplify.simplify_terms srk phi in
  let solver = Smt.mk_solver srk in
  let uninterp_phi =
    rewrite srk
      ~down:(nnf_rewriter srk)
      ~up:(Nonlinear.uninterpret_rewriter srk)
      phi
  in
  let (lin_phi, nonlinear) = SrkSimplify.purify srk uninterp_phi in
  let nonlinear_defs =
    Symbol.Map.enum nonlinear
    /@ (fun (symbol, expr) ->
        match Expr.refine srk expr with
        | `Term t -> mk_eq srk (mk_const srk symbol) t
        | `Formula phi -> mk_iff srk (mk_const srk symbol) phi)
    |> BatList.of_enum
  in
  let nonlinear = Symbol.Map.map (Nonlinear.interpret srk) nonlinear in
  let rec replace_defs_term term =
    substitute_const
      srk
      (fun x ->
         try replace_defs_term (Symbol.Map.find x nonlinear)
         with Not_found -> mk_const srk x)
      term
  in
  let replace_defs =
    substitute_const
      srk
      (fun x ->
         try replace_defs_term (Symbol.Map.find x nonlinear)
         with Not_found -> mk_const srk x)
  in
  Smt.Solver.add solver [lin_phi];
  Smt.Solver.add solver nonlinear_defs;
  let integrity psi =
    Smt.Solver.add solver [Nonlinear.uninterpret srk psi]
  in
  let rec go () =
    match Smt.Solver.get_model solver with
    | `Unsat -> `Unsat
    | `Unknown -> `Unknown
    | `Sat model ->
      match Interpretation.select_implicant model lin_phi with
      | None -> assert false
      | Some implicant ->
        let cs = CS.mk_empty srk in
        let constraint_partition =
          List.map replace_defs implicant
          |> Polyhedron.of_implicant ~admit:true cs
          |> Polyhedron.try_fourier_motzkin cs (fun _ -> false)
          |> Polyhedron.implicant_of cs
          |> SrkSimplify.partition_implicant
        in
        let is_sat constraints =
          let wedge = of_atoms srk constraints in
          strengthen ~integrity wedge;
          not (is_bottom wedge)
        in
        if List.for_all is_sat constraint_partition then
          `Unknown
        else
          go ()
  in
  if Symbol.Map.is_empty nonlinear then
    Smt.Solver.check solver []
  else
    go ()

let abstract ?exists:(p=fun x -> true) ?(subterm=fun x -> true) srk phi =
  let phi = eliminate_ite srk phi in
  let phi = SrkSimplify.simplify_terms srk phi in
  logf "Abstracting formula@\n%a"
    (Formula.pp srk) phi;
  let solver = Smt.mk_solver srk in
  let uninterp_phi =
    rewrite srk
      ~down:(nnf_rewriter srk)
      ~up:(Nonlinear.uninterpret_rewriter srk)
      phi
  in
  let (lin_phi, nonlinear) = SrkSimplify.purify srk uninterp_phi in
  let nonlinear_defs =
    Symbol.Map.enum nonlinear
    /@ (fun (symbol, expr) ->
        match Expr.refine srk expr with
        | `Term t -> mk_eq srk (mk_const srk symbol) t
        | `Formula phi -> mk_iff srk (mk_const srk symbol) phi)
    |> BatList.of_enum
    |> mk_and srk
  in
  let nonlinear = Symbol.Map.map (Nonlinear.interpret srk) nonlinear in
  let rec replace_defs_term term =
    substitute_const
      srk
      (fun x ->
         try replace_defs_term (Symbol.Map.find x nonlinear)
         with Not_found -> mk_const srk x)
      term
  in
  let replace_defs =
    substitute_const
      srk
      (fun x ->
         try replace_defs_term (Symbol.Map.find x nonlinear)
         with Not_found -> mk_const srk x)
  in
  Smt.Solver.add solver [lin_phi];
  Smt.Solver.add solver [nonlinear_defs];
  let integrity psi =
    Smt.Solver.add solver [Nonlinear.uninterpret srk psi]
  in
  let rec go wedge =
    let blocking_clause =
      to_formula wedge
      |> Nonlinear.uninterpret srk
      |> mk_not srk
    in
    logf ~level:`trace "Blocking clause %a" (Formula.pp srk) blocking_clause;
    Smt.Solver.add solver [blocking_clause];
    match Smt.Solver.get_model solver with
    | `Unsat -> wedge
    | `Unknown ->
      logf ~level:`warn "Symbolic abstraction failed; returning top";
      top srk
    | `Sat model ->
      match Interpretation.select_implicant model lin_phi with
      | None -> assert false
      | Some implicant ->
        let cs = CoordinateSystem.mk_empty srk in
        let implicant' =
          List.map replace_defs implicant
          |> Polyhedron.of_implicant ~admit:true cs
          |> Polyhedron.try_fourier_motzkin cs p
          |> Polyhedron.implicant_of cs
        in
        let new_wedge =
          implicant'
          |> of_atoms srk
          |> exists ~integrity ~subterm p
        in
        if is_bottom wedge then begin
          strengthen ~integrity new_wedge;
          go new_wedge
        end else
          go (join ~integrity wedge new_wedge)
  in
  let result = go (bottom srk) in
  logf "Abstraction result:@\n%a" pp result;
  result

let ensure_min_max srk =
  List.iter
    (fun (name, typ) ->
       if not (is_registered_name srk name) then
         register_named_symbol srk name typ)
    [("min", `TyFun ([`TyReal; `TyReal], `TyReal));
     ("max", `TyFun ([`TyReal; `TyReal], `TyReal))]

let symbolic_bounds_formula ?exists:(p=fun x -> true) srk phi symbol =
  let phi = eliminate_ite srk phi in
  ensure_min_max srk;
  let min = get_named_symbol srk "min" in
  let max = get_named_symbol srk "max" in
  let mk_min x y =
    match Term.destruct srk x, Term.destruct srk y with
    | `Real xr, `Real yr -> mk_real srk (QQ.min xr yr)
    | _, _ -> mk_app srk min [x; y]
  in
  let mk_max x y =
    match Term.destruct srk x, Term.destruct srk y with
    | `Real xr, `Real yr -> mk_real srk (QQ.max xr yr)
    | _, _ -> mk_app srk max [x; y]
  in

  let symbol_term = mk_const srk symbol in
  let subterm x = x != symbol in
  let solver = Smt.mk_solver srk in
  let uninterp_phi =
    rewrite srk
      ~down:(nnf_rewriter srk)
      ~up:(Nonlinear.uninterpret_rewriter srk)
      phi
  in
  let (lin_phi, nonlinear) = SrkSimplify.purify srk uninterp_phi in
  let nonlinear_defs =
    Symbol.Map.enum nonlinear
    /@ (fun (symbol, expr) ->
        match Expr.refine srk expr with
        | `Term t -> mk_eq srk (mk_const srk symbol) t
        | `Formula phi -> mk_iff srk (mk_const srk symbol) phi)
    |> BatList.of_enum
    |> mk_and srk
  in
  let nonlinear = Symbol.Map.map (Nonlinear.interpret srk) nonlinear in
  let rec replace_defs_term term =
    substitute_const
      srk
      (fun x ->
         try replace_defs_term (Symbol.Map.find x nonlinear)
         with Not_found -> mk_const srk x)
      term
  in
  let replace_defs =
    substitute_const
      srk
      (fun x ->
         try replace_defs_term (Symbol.Map.find x nonlinear)
         with Not_found -> mk_const srk x)
  in
  Smt.Solver.add solver [lin_phi];
  Smt.Solver.add solver [nonlinear_defs];
  let integrity psi =
    Smt.Solver.add solver [Nonlinear.uninterpret srk psi]
  in
  let rec go (lower, upper) =
    match Smt.Solver.get_model solver with
    | `Unsat -> (lower, upper)
    | `Unknown ->
      logf ~level:`warn "Symbolic abstraction failed; returning top";
      ([[]], [[]])
    | `Sat model ->
      match Interpretation.select_implicant model lin_phi with
      | None -> assert false
      | Some implicant ->
        let (wedge_lower, wedge_upper) =
          let cs = CoordinateSystem.mk_empty srk in
          let implicant' =
            List.map replace_defs implicant
            |> Polyhedron.of_implicant ~admit:true cs
            |> Polyhedron.try_fourier_motzkin cs p
            |> Polyhedron.implicant_of cs
          in
          let wedge =
            implicant'
            |> of_atoms srk
            |> exists ~integrity ~subterm p
          in
          if CS.admits wedge.cs (mk_const srk symbol) then
            symbolic_bounds wedge symbol
          else
            ([], [])
        in
        let lower_blocking =
          List.map
            (fun lower_bound -> mk_lt srk symbol_term lower_bound)
            wedge_lower
          |> List.map (Nonlinear.uninterpret srk)
          |> mk_or srk
        in
        let upper_blocking =
          List.map
            (fun upper_bound -> mk_lt srk upper_bound symbol_term)
            wedge_upper
          |> List.map (Nonlinear.uninterpret srk)
          |> mk_or srk
        in
        Smt.Solver.add solver [mk_or srk [lower_blocking; upper_blocking]];
        go (wedge_lower::lower, wedge_upper::upper)
  in
  let (lower, upper) = go ([], []) in
  if lower = [] then
    `Unsat
  else
    let lower =
      if List.mem [] lower then
        None
    else
      Some (BatList.reduce mk_min (List.map (BatList.reduce mk_max) lower))
    in
    let upper =
      if List.mem [] upper then
        None
      else
        Some (BatList.reduce mk_max (List.map (BatList.reduce mk_min) upper))
    in
    `Sat (lower, upper)

let symbolic_bounds_formula ?(exists=fun x -> true) srk phi symbol =
  Log.time "symbolic_bounds_formula" (symbolic_bounds_formula ~exists srk phi) symbol

let bounds wedge term =
  if CS.admits wedge.cs term then
    bound_vec wedge (CS.vec_of_term wedge.cs term)
  else
    Interval.top

let coordinate_system wedge = wedge.cs

let polyhedron wedge =
  let open Lincons0 in
  BatArray.enum (Abstract0.to_lincons_array (get_manager ()) wedge.abstract)
  |> BatEnum.filter_map (fun lcons ->
      match lcons.typ with
      | SUPEQ | SUP -> Some (`Geq, vec_of_linexpr wedge.env lcons.linexpr0)
      | EQ -> Some (`Eq, vec_of_linexpr wedge.env lcons.linexpr0)
      | _ -> None)
  |> BatList.of_enum
