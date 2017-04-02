open Syntax
open Apak
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

include Log.Make(struct let name = "ark.cube" end)

module Int = struct
  type t = int [@@deriving show,ord]
  let tag k = k
end

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

module IntMap = Apak.Tagged.PTMap(Int)
module IntSet = Apak.Tagged.PTSet(Int)

(* An sd_term is a term with synthetic dimensions, which can itself be used to
   define a synthetic dimension.  And sd_term should be interpreted within the
   context of an environment that maps positive integers to (synthetic)
   dimensions: the vectors that appear in an sd_term represent affine terms
   over these dimensions, with the special dimension (-1) corresponding to the
   number 1.  *)
type sd_term = Mul of V.t * V.t
             | Inv of V.t
             | Mod of V.t * V.t
             | Floor of V.t
             | App of symbol * (V.t list)

(* Env needs to map a set of synthetic terms into an initial segment of the
   naturals, with all of the integer-typed synthetic terms mapped to smaller
   naturals than real-typed synthetic terms *)
module Env = struct
  module A = BatDynArray

  type 'a t =
    { ark : 'a context;
      term_id : (sd_term, int) Hashtbl.t;
      id_def : (sd_term * int * [`TyInt | `TyReal]) A.t;
      int_dim : int A.t;
      real_dim : int A.t }

  let const_id = -1

  let int_dim env = A.length env.int_dim

  let real_dim env = A.length env.real_dim

  let dim env = int_dim env + real_dim env

  let mk_empty ark =
    { ark = ark;
      term_id = Hashtbl.create 991;
      id_def = A.create ();
      int_dim = A.create ();
      real_dim = A.create () }

  let copy env =
    { ark = env.ark;
      term_id = Hashtbl.copy env.term_id;
      id_def = A.copy env.id_def;
      int_dim = A.copy env.int_dim;
      real_dim = A.copy env.real_dim }

  let sd_term_of_id env id =
    let (term, _, _) = A.get env.id_def id in
    term

  let rec term_of_id env id =
    match sd_term_of_id env id with
    | Mul (x, y) -> mk_mul env.ark [term_of_vec env x; term_of_vec env y]
    | Inv x -> mk_div env.ark (mk_real env.ark QQ.one) (term_of_vec env x)
    | Mod (x, y) -> mk_mod env.ark (term_of_vec env x) (term_of_vec env y)
    | Floor x -> mk_floor env.ark (term_of_vec env x)
    | App (func, args) -> mk_app env.ark func (List.map (term_of_vec env) args)

  and term_of_vec env vec =
    (V.enum vec)
    /@ (fun (coeff, id) ->
        if id = const_id then
          mk_real env.ark coeff
        else if QQ.equal QQ.one coeff then
          term_of_id env id
        else
          mk_mul env.ark [mk_real env.ark coeff; term_of_id env id])
    |> BatList.of_enum
    |> mk_add env.ark

  let level_of_id env id =
    let (_, level, _) = A.get env.id_def id in
    level

  let type_of_id env id =
    let (_, _, typ) = A.get env.id_def id in
    typ

  let dim_of_id env id =
    let intd = A.length env.int_dim in
    match type_of_id env id with
    | `TyInt -> ArkUtil.search id env.int_dim
    | `TyReal -> intd + (ArkUtil.search id env.real_dim)

  let id_of_dim env dim =
    let intd = A.length env.int_dim in
    try
      if dim >= intd then
        A.get env.real_dim (dim - intd)
      else
        A.get env.int_dim dim
    with BatDynArray.Invalid_arg _ ->
      invalid_arg "Env.id_of_dim: out of bounds"

  let level_of_vec env vec =
    BatEnum.fold
      (fun level (_, id) ->
         if id = const_id then
           level
         else
           max level (level_of_id env id))
      (-1)
      (V.enum vec)

  let type_of_vec env vec =
    let is_integral (coeff, id) =
      QQ.to_zz coeff != None
      && (id = const_id || type_of_id env id = `TyInt)
    in
    if BatEnum.for_all is_integral (V.enum vec) then
      `TyInt
    else
      `TyReal

  let join_typ s t = match s,t with
    | `TyInt, `TyInt -> `TyInt
    | _, _ -> `TyReal

  let ark env = env.ark

  let pp formatter env =
    Format.fprintf formatter "[@[<v 0>";
    env.id_def |> A.iteri (fun id _ ->
        Format.fprintf formatter "%d -> %a (%d, %s)@;"
          id
          (Term.pp env.ark) (term_of_id env id)
          (dim_of_id env id)
          (match type_of_id env id with | `TyInt -> "int" | `TyReal -> "real"));
    Format.fprintf formatter "@]]"

  let rec pp_vector env formatter vec =
    let pp_elt formatter (k, id) =
      if id = const_id then
        QQ.pp formatter k
      else if QQ.equal k QQ.one then
        pp_sd_term env formatter (sd_term_of_id env id)
      else
        Format.fprintf formatter "%a@ * (@[%a@])"
          QQ.pp k
          (pp_sd_term env) (sd_term_of_id env id)
    in
    let pp_sep formatter () = Format.fprintf formatter " +@ " in
    if V.is_zero vec then
      Format.pp_print_string formatter "0"
    else
      Format.fprintf formatter "@[<hov 1>%a@]"
        (ApakEnum.pp_print_enum ~pp_sep pp_elt) (V.enum vec)

  and pp_sd_term env formatter = function
    | Mul (x, y) ->
      Format.fprintf formatter "@[<hov 1>(%a)@ * (%a)@]"
        (pp_vector env) x
        (pp_vector env) y
    | Inv x ->
      Format.fprintf formatter "1/(@[<hov 1>%a@])"
        (pp_vector env) x
    | Mod (x, y) ->
      Format.fprintf formatter "@[<hov 1>(%a)@ mod (%a)@]"
        (pp_vector env) x
        (pp_vector env) y
    | Floor x ->
      Format.fprintf formatter "floor(@[%a@])"
        (pp_vector env) x
    | App (const, []) ->
      Format.fprintf formatter "%a" (pp_symbol env.ark) const
    | App (func, args) ->
      let pp_comma formatter () = Format.fprintf formatter ",@ " in
      Format.fprintf formatter "%a(@[<hov 1>%a@])"
        (pp_symbol env.ark) func
        (ApakEnum.pp_print_enum ~pp_sep:pp_comma (pp_vector env))
        (BatList.enum args)

  let get_term_id ?(register=true) env t =
    if Hashtbl.mem env.term_id t then
      Hashtbl.find env.term_id t
    else if register then
      let id = A.length env.id_def in
      let (typ, level) = match t with
        | Mul (s, t) | Mod (s, t) ->
          (join_typ (type_of_vec env s) (type_of_vec env t),
           max (level_of_vec env s) (level_of_vec env t))
        | Floor x ->
          (`TyInt, level_of_vec env x)
        | Inv x ->
          (`TyReal, level_of_vec env x)
        | App (func, args) ->
          let typ =
            match typ_symbol env.ark func with
            | `TyFun (_, `TyInt) | `TyInt -> `TyInt
            | `TyFun (_, `TyReal) | `TyReal -> `TyReal
            | `TyFun (_, `TyBool) | `TyBool -> `TyInt
          in
          let level =
            List.fold_left max 0 (List.map (level_of_vec env) args)
          in
          (typ, level)
      in
      A.add env.id_def (t, level, typ);
      Hashtbl.add env.term_id t id;
      begin match typ with
        | `TyInt -> A.add env.int_dim id
        | `TyReal -> A.add env.real_dim id
      end;
      logf ~level:`trace "Registered %s: %d -> %a"
        (match typ with `TyInt -> "int" | `TyReal -> "real")
        id
        (pp_sd_term env) t;
      id
    else
      raise Not_found

  let const_of_vec vec =
    let (const_coeff, rest) = V.pivot const_id vec in
    if V.is_zero rest then
      Some const_coeff
    else
      None

  let vec_of_term ?(register=true) env =
    let rec alg = function
      | `Real k -> V.of_term k const_id
      | `App (symbol, []) ->
        V.of_term QQ.one (get_term_id ~register env (App (symbol, [])))

      | `App (symbol, xs) ->
        let xs =
          List.map (fun x ->
              match refine env.ark x with
              | `Term t -> Term.eval env.ark alg t
              | `Formula _ -> assert false (* TODO *))
            xs
        in
        V.of_term QQ.one (get_term_id ~register env (App (symbol, xs)))

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
              V.of_term QQ.one (get_term_id ~register env (Mul (x, y)))
            in
            V.scalar_mul k (List.fold_left mul x xs)
        end
      | `Binop (`Div, x, y) ->
        let denomenator = V.of_term QQ.one (get_term_id ~register env (Inv y)) in
        let (k, xrest) = V.pivot const_id x in
        if V.equal xrest V.zero then
          V.scalar_mul k denomenator
        else
          V.of_term QQ.one (get_term_id ~register env (Mul (x, denomenator)))
      | `Binop (`Mod, x, y) ->
        V.of_term QQ.one (get_term_id ~register env (Mod (x, y)))
      | `Unop (`Floor, x) ->
        V.of_term QQ.one (get_term_id ~register env (Floor x))
      | `Unop (`Neg, x) -> V.negate x
      | `Ite (_, _, _) -> assert false (* No ites in implicants *)
    in
    Term.eval env.ark alg

  let mem_term env t =
    try
      ignore (vec_of_term ~register:false env t);
      true
    with Not_found -> false

  let vec_of_linexpr env linexpr =
    let vec = ref V.zero in
    Linexpr0.iter (fun coeff dim ->
        match qq_of_coeff coeff with
        | Some qq ->
          vec := V.add_term qq (id_of_dim env dim) (!vec)
        | None -> assert false)
      linexpr;
    match qq_of_coeff (Linexpr0.get_cst linexpr) with
    | Some qq -> V.add_term qq const_id (!vec)
    | None -> assert false

  let linexpr_of_vec env vec =
    let mk (coeff, id) = (coeff_of_qq coeff, dim_of_id env id) in
    let (const_coeff, rest) = V.pivot const_id vec in
    Linexpr0.of_list None
      (BatList.of_enum (BatEnum.map mk (V.enum rest)))
      (Some (coeff_of_qq const_coeff))

  let term_of_polynomial env p =
    (P.enum p)
    /@ (fun (coeff, monomial) ->
        let product =
          BatEnum.fold
            (fun product (id, power) ->
               let term = term_of_id env id in
               BatEnum.fold
                 (fun product _ -> term::product)
                 product
                 (1 -- power))
            [mk_real env.ark coeff]
            (Monomial.enum monomial)
        in
        mk_mul env.ark product)
    |> BatList.of_enum
    |> mk_add env.ark
end

let pp_vector = Env.pp_vector
let pp_sd_term = Env.pp_sd_term

let vec_of_poly = P.vec_of ~const:Env.const_id
let poly_of_vec = P.of_vec ~const:Env.const_id

let get_manager =
  let manager = ref None in
  fun () ->
    match !manager with
    | Some man -> man
    | None ->
      let man = Polka.manager_alloc_strict () in
      manager := Some man;
      man

type 'a t =
  { env : 'a Env.t;
    mutable abstract : (Polka.strict Polka.t) Abstract0.t;
    (* int_dim and real_dim keep track of the number of dimensions in the
       abstract value associated with a cube, which can get out of sync with the
       number of dimensions known to the environment (by registering new terms).
       update_env gets them back into sync *)
    mutable int_dim : int;
    mutable real_dim : int; }

let pp formatter property =
  Abstract0.print
    (fun dim ->
       Apak.Putil.mk_show
         (pp_sd_term property.env)
         (Env.sd_term_of_id property.env (Env.id_of_dim property.env dim)))
    formatter
    property.abstract

let show property = Apak.Putil.mk_show pp property

(* Should be called when new terms are registered in the environment attached
   to a cube *)
let update_env cube =
  let int_dim = Env.int_dim cube.env in
  let real_dim = Env.real_dim cube.env in
  let added_int = max 0 (int_dim - cube.int_dim) in
  let added_real = max 0 (real_dim - cube.real_dim) in
  let added =
    BatEnum.append
      ((1 -- added_int) /@ (fun _ -> cube.int_dim))
      ((1 -- added_real) /@ (fun _ -> cube.int_dim + cube.real_dim))
    |> BatArray.of_enum
  in
  if added_int + added_real > 0 then begin
    logf "update env: adding %d integer and %d real dimension(s)"
      added_int
      added_real;
    let abstract =
      Abstract0.add_dimensions
        (get_manager ())
        cube.abstract
        { Dim.dim = added;
          Dim.intdim = added_int;
          Dim.realdim = added_real }
        false
    in
    cube.abstract <- abstract;
    cube.int_dim <- int_dim;
    cube.real_dim <- real_dim
  end

let top context =
  { env = Env.mk_empty context;
    abstract = Abstract0.top (get_manager ()) 0 0;
    int_dim = 0;
    real_dim = 0 }

let is_top property = Abstract0.is_top (get_manager ()) property.abstract

let bottom context =
  { env = Env.mk_empty context;
    abstract = Abstract0.bottom (get_manager ()) 0 0;
    int_dim = 0;
    real_dim = 0 }

let is_bottom property = Abstract0.is_bottom (get_manager ()) property.abstract

let to_atoms property =
  let open Lincons0 in
  let ark = Env.ark property.env in
  let zero = mk_real ark QQ.zero in
  BatArray.enum (Abstract0.to_lincons_array (get_manager ()) property.abstract)
  /@ (fun lincons ->
      let term =
        Env.vec_of_linexpr property.env lincons.linexpr0
        |> Env.term_of_vec property.env
      in
      match lincons.typ with
      | EQ -> mk_eq ark term zero
      | SUPEQ -> mk_leq ark zero term
      | SUP -> mk_lt ark zero term
      | DISEQ | EQMOD _ -> assert false)
  |> BatList.of_enum

let to_formula property =
  let ark = Env.ark property.env in
  mk_and ark (to_atoms property)

let lincons_of_atom env atom =
  let ark = Env.ark env in
  match Interpretation.destruct_atom ark atom with
  | `Comparison (`Lt, x, y) ->
    Lincons0.make
      (Env.linexpr_of_vec
         env
         (V.add (Env.vec_of_term env y) (V.negate (Env.vec_of_term env x))))
      Lincons0.SUP
  | `Comparison (`Leq, x, y) ->
    Lincons0.make
      (Env.linexpr_of_vec
         env
         (V.add (Env.vec_of_term env y) (V.negate (Env.vec_of_term env x))))
      Lincons0.SUPEQ
  | `Comparison (`Eq, x, y) ->
    Lincons0.make
      (Env.linexpr_of_vec
         env
         (V.add (Env.vec_of_term env y) (V.negate (Env.vec_of_term env x))))
      Lincons0.EQ
  | `Literal (_, _) -> assert false

let bound_vec property vec =
  Abstract0.bound_linexpr
    (get_manager ())
    property.abstract
    (Env.linexpr_of_vec property.env vec)
  |> Interval.of_apron

(* Test whether property |= x = y *)
let sat_vec_equation property x y =
  let eq_constraint =
    Lincons0.make
      (Env.linexpr_of_vec property.env (V.add x (V.negate y)))
      Lincons0.EQ
  in
  Abstract0.sat_lincons (get_manager ()) property.abstract eq_constraint

let apron_farkas abstract =
  let open Lincons0 in
  let constraints =
    Abstract0.to_lincons_array (get_manager ()) abstract
  in
  let lambda_constraints =
    (0 -- (Array.length constraints - 1)) |> BatEnum.filter_map (fun dim ->
        match constraints.(dim).typ with
        | SUP | SUPEQ ->
          let lincons =
            Lincons0.make
              (Linexpr0.of_list None [(coeff_of_qq QQ.one, dim)] None)
              SUPEQ
          in
          Some lincons
        | EQ -> None
        | DISEQ | EQMOD _ -> assert false)
    |> BatArray.of_enum
  in
  let lambda_abstract =
    Abstract0.of_lincons_array
      (get_manager ())
      0
      (Array.length constraints)
      lambda_constraints
  in
  let nb_columns =
    let dim = Abstract0.dimension (get_manager ()) abstract in
    (* one extra column for the constant *)
    dim.Dim.intd + dim.Dim.reald + 1
  in
  let columns =
    Array.init nb_columns (fun _ -> Linexpr0.make None)
  in
  for row = 0 to Array.length constraints - 1 do
    constraints.(row).linexpr0 |> Linexpr0.iter (fun coeff col ->
        Linexpr0.set_coeff columns.(col) row coeff);
    Linexpr0.set_coeff
      columns.(nb_columns - 1)
      row
      (Linexpr0.get_cst constraints.(row).linexpr0)
  done;
  (lambda_abstract, columns)

let affine_hull property =
  let open Lincons0 in
  BatArray.enum (Abstract0.to_lincons_array (get_manager ()) property.abstract)
  |> BatEnum.filter_map (fun lcons ->
      match lcons.typ with
      | EQ -> Some (Env.vec_of_linexpr property.env lcons.linexpr0)
      | _ -> None)
  |> BatList.of_enum

let strengthen ?integrity:(integrity=(fun _ -> ())) property =
  let env = property.env in
  let ark = Env.ark env in
  let zero = mk_real ark QQ.zero in
  let add_bound_unsafe bound =
    let abstract =
      Abstract0.meet_lincons_array
        (get_manager ())
        property.abstract
        [| lincons_of_atom env bound |]
    in
    property.abstract <- abstract
  in
  let add_bound precondition bound =
    logf ~level:`info "Integrity: %a => %a"
      (Formula.pp ark) precondition
      (Formula.pp ark) bound;
    integrity (mk_or ark [mk_not ark precondition; bound]);

    ignore (lincons_of_atom env bound);
    update_env property;
    add_bound_unsafe bound
  in

  logf "Before strengthen: %a" pp property;

  let cube_affine_hull = affine_hull property in
  let affine_hull_formula =
    ref (cube_affine_hull
         |> List.map (fun vec -> mk_eq ark (Env.term_of_vec property.env vec) zero)
         |> mk_and ark)
  in
  (* Rewrite maintains a Grobner basis for the coordinate ideal + the ideal of
     polynomials vanishing on the underlying polyhedron of the cube *)
  let rewrite =
    let polyhedron_ideal =
      List.map poly_of_vec cube_affine_hull
    in
    let coordinate_ideal =
      BatEnum.filter_map (fun id ->
          match Env.sd_term_of_id property.env id with
          | Mul (x, y) ->
            Some (P.sub
                    (P.of_dim id)
                    (P.mul (poly_of_vec x) (poly_of_vec y)))
          | Inv x ->
            Some (P.sub (P.mul (poly_of_vec x) (P.of_dim id)) (P.scalar QQ.one))
          | _ -> None)
        (0 -- (Env.dim property.env - 1))
      |> BatList.of_enum
    in
    ref (polyhedron_ideal@coordinate_ideal
         |> Polynomial.Rewrite.mk_rewrite Monomial.degrevlex
         |> Polynomial.Rewrite.grobner_basis)
  in
  let pp_dim formatter i =
    Term.pp ark formatter (Env.term_of_id property.env i)
  in
  logf "Rewrite: @[<v 0>%a@]" (Polynomial.Rewrite.pp pp_dim) (!rewrite);
  let reduce_vec vec =
    Polynomial.Rewrite.reduce (!rewrite) (poly_of_vec vec)
    |> Env.term_of_polynomial property.env
  in

  (* Equational saturation.  A polyhedron P is equationally saturated if every
     degree-1 polynomial in the ideal of polynomials vanishing on P + the
     coordinate ideal vanishes on P.  This procedure computes the greatest
     equationally saturated polyhedron contained in the underlying cube of the
     polyhedron.  *)
  let saturated = ref false in

  (* Hashtable mapping canonical forms of nonlinear terms to their
     representative terms. *)
  let canonical = ExprHT.create 991 in
  while not !saturated do
    saturated := true;
    for id = 0 to Env.dim property.env - 1 do
      let term = Env.term_of_id property.env id in
      (* TODO: track the equations that were actually used in reductions rather
         than just using the affine hull as the precondition. *)
      let reduced_id =
        match vec_of_poly (Polynomial.Rewrite.reduce (!rewrite) (P.of_dim id)) with
        | Some p -> p
        | None ->
          (* Reducing a linear polynomial must result in another linear polynomial *)
          assert false
      in
      let reduced_term = Env.term_of_vec property.env reduced_id in
      add_bound (!affine_hull_formula) (mk_eq ark term reduced_term);

      (* congruence closure *)
      let add_canonical reduced =
        (* Add [reduced->term] to the canonical map.  Or if there's already a
           mapping [reduced->rep], add the equation rep=term *)
        if ExprHT.mem canonical reduced then
          (* Don't need an integrity formula (congruence is free), so don't call add_bound. *)
          add_bound_unsafe (mk_eq ark term (ExprHT.find canonical reduced))
        else
          ExprHT.add canonical reduced term
      in
      begin match Env.sd_term_of_id property.env id with
      | App (_, []) | Mul (_, _) -> ()
      | App (func, args) ->
        add_canonical (mk_app ark func (List.map reduce_vec args))
      | Inv t ->
        add_canonical (mk_div ark (mk_real ark QQ.one) (reduce_vec t))
      | Mod (num, den) ->
        add_canonical (mk_mod ark (reduce_vec num) (reduce_vec den))
      | Floor t ->
        add_canonical (mk_floor ark (reduce_vec t))
      end;
    done;
    (* Check for new polynomials vanishing on the underlying polyhedron *)
    affine_hull property |> List.iter (fun vec ->
        let reduced =
          Polynomial.Rewrite.reduce (!rewrite) (poly_of_vec vec)
        in
        if not (P.equal P.zero reduced) then begin
          let reduced_term = Env.term_of_polynomial property.env reduced in
          saturated := false;
          rewrite := Polynomial.Rewrite.add_saturate (!rewrite) reduced;
          affine_hull_formula := mk_and ark [!affine_hull_formula;
                                             mk_eq ark reduced_term zero]
        end);
  done;

  (* Compute bounds for synthetic dimensions using the bounds of their
     operands *)
  for id = 0 to Env.dim property.env - 1 do
    let term = Env.term_of_id property.env id in
    match Env.sd_term_of_id property.env id with
    | Mul (x, y) ->
    let go (x,x_ivl,x_term) (y,y_ivl,y_term) =
        if Interval.is_nonnegative y_ivl then
          begin
            let y_nonnegative = mk_leq ark (mk_real ark QQ.zero) y_term in
            (match Interval.lower x_ivl with
             | Some lo ->
               add_bound
                 (mk_and ark [y_nonnegative; mk_leq ark (mk_real ark lo) x_term])
                 (mk_leq ark (Env.term_of_vec env (V.scalar_mul lo y)) term)
             | None -> ());
            (match Interval.upper x_ivl with
             | Some hi ->
               add_bound
                 (mk_and ark [y_nonnegative; mk_leq ark x_term (mk_real ark hi)])
                 (mk_leq ark term (Env.term_of_vec env (V.scalar_mul hi y)))

             | None -> ())
          end
        else if Interval.is_nonpositive y_ivl then
          begin
            let y_nonpositive = mk_leq ark y_term (mk_real ark QQ.zero) in
            (match Interval.lower x_ivl with
             | Some lo ->
               add_bound
                 (mk_and ark [y_nonpositive; mk_leq ark (mk_real ark lo) x_term])
                 (mk_leq ark term (Env.term_of_vec env (V.scalar_mul lo y)));
             | None -> ());
            (match Interval.upper x_ivl with
             | Some hi ->
               add_bound
                 (mk_and ark [y_nonpositive; mk_leq ark x_term (mk_real ark hi)])
                 (mk_leq ark (Env.term_of_vec env (V.scalar_mul hi y)) term);
             | None -> ())
          end
        else
          ()
      in

      let x_ivl = bound_vec property x in
      let y_ivl = bound_vec property y in
      let x_term = Env.term_of_vec env x in
      let y_term = Env.term_of_vec env y in

      go (x,x_ivl,x_term) (y,y_ivl,y_term);
      go (y,y_ivl,y_term) (x,x_ivl,x_term);

      let mul_ivl = Interval.mul x_ivl y_ivl in
      let mk_ivl x interval =
        let lower =
          match Interval.lower interval with
          | Some lo -> mk_leq ark (mk_real ark lo) x
          | None -> mk_true ark
        in
        let upper =
          match Interval.upper interval with
          | Some hi -> mk_leq ark x (mk_real ark hi)
          | None -> mk_true ark
        in
        mk_and ark [lower; upper]
      in
      let precondition =
        mk_and ark [mk_ivl x_term x_ivl; mk_ivl y_term y_ivl]
      in
      (match Interval.lower mul_ivl with
       | Some lo -> add_bound precondition (mk_leq ark (mk_real ark lo) term)
       | None -> ());
      (match Interval.upper mul_ivl with
       | Some hi -> add_bound precondition (mk_leq ark term (mk_real ark hi))
       | None -> ())

    | Floor x ->
      let x_term = Env.term_of_vec env x in
      let _true = mk_true ark in
      add_bound _true (mk_leq ark term x_term);
      add_bound _true (mk_lt ark
                         (mk_add ark [x_term; mk_real ark (QQ.of_int (-1))])
                         term)

    (* TO DO *)
    | Div (x, y) -> ()
    | Mod (x, y) -> ()
    | App (func, args) -> ()
  done;

  (* Use bounds on synthetic dimensions to compute bounds on operands.  For
     example, if we have x*y <= 10*x and x is non-negative, then we can infer
     y <= 10. *)
  let (lambda_constraints, columns) =
    try
      apron_farkas property.abstract
    with Invalid_argument _ -> assert false
  in
  let kcolumn = Array.length columns - 1 in

  (* find optimal [a,b] s.t. prop |= a*x <= sd <= b*x *)
  let implied_coeff_interval sd x =
    let col_constraints =
      Array.map
        (fun column -> Lincons0.make column Lincons0.EQ)
        columns
    in
    (* replace x, sd, and constant column constraint with trivial ones *)
    let trivial = Lincons0.make (Linexpr0.make None) Lincons0.EQ in
    col_constraints.(Env.dim_of_id env x) <- trivial;
    col_constraints.(Env.dim_of_id env sd) <- trivial;
    col_constraints.(kcolumn) <- trivial;

    let feasible =
      Abstract0.meet_lincons_array
        (get_manager ())
        lambda_constraints
        col_constraints
    in
    let x_col_bounds feasible =
      Abstract0.bound_linexpr
        (get_manager ())
        feasible
        columns.(Env.dim_of_id env x)
      |> Interval.of_apron
    in

    let upper =
      let sd_column_minus_one = Linexpr0.copy columns.(Env.dim_of_id env sd) in
      Linexpr0.set_cst sd_column_minus_one (coeff_of_qq QQ.one);

      let neg_const_column = Linexpr0.make None in
      columns.(kcolumn) |> Linexpr0.iter (fun coeff dim ->
          Linexpr0.set_coeff neg_const_column dim (Coeff.neg coeff));

      let feasible_upper =
        Abstract0.meet_lincons_array
          (get_manager ())
          feasible
          [| Lincons0.make sd_column_minus_one Lincons0.EQ;
             Lincons0.make neg_const_column Lincons0.SUPEQ |]
      in
      let ivl = x_col_bounds feasible_upper in
      if Interval.equal ivl Interval.bottom then
        None
      else
        match Interval.lower ivl with
        | Some lower -> Some lower
        | None -> None
    in
    let lower =
      let sd_column_one = Linexpr0.copy columns.(Env.dim_of_id env sd) in
      Linexpr0.set_cst sd_column_one (coeff_of_qq (QQ.of_int (-1)));
      let feasible_lower =
        Abstract0.meet_lincons_array
          (get_manager ())
          feasible
          [| Lincons0.make sd_column_one Lincons0.EQ;
             Lincons0.make columns.(kcolumn) Lincons0.SUPEQ |]
      in
      let ivl = x_col_bounds feasible_lower in
      if Interval.equal ivl Interval.bottom then
        None
      else
        match Interval.upper ivl with
        | Some upper -> Some (QQ.negate upper)
        | None -> None
    in
    (lower, upper)
  in

  (* sd represents the term x*y.  add_coeff_bounds finds bounds for y that
     are implied by bounds for x*y. *)
  let add_coeff_bounds sd x y =
    let x_ivl = bound_vec property (V.of_term QQ.one x) in
    let x_term = Env.term_of_id env x in
    let y_term = Env.term_of_id env y in
    let sd_term = Env.term_of_id env sd in

    if Interval.is_nonnegative x_ivl then begin (* 0 <= x *)
      let (a_lo, a_hi) = implied_coeff_interval sd x in
      begin match a_lo with
        | None -> ()
        | Some lo ->
          add_bound
            (mk_and ark [mk_leq ark (mk_real ark QQ.zero) x_term;
                         mk_leq ark
                           (mk_mul ark [mk_real ark lo; x_term])
                           sd_term])
            (mk_leq ark (mk_real ark lo) y_term)
      end;
      begin match a_hi with
        | None -> ()
        | Some hi ->
          add_bound
            (mk_and ark [mk_leq ark (mk_real ark QQ.zero) x_term;
                         mk_leq ark
                           sd_term
                           (mk_mul ark [mk_real ark hi; x_term])])
            (mk_leq ark y_term (mk_real ark hi))
      end
      (* to do: add bounds for the x <= 0 case as well *)
    end
  in

  for id = 0 to Env.dim env - 1 do
    let id_of_vec vec =
      match BatList.of_enum (V.enum vec) with
      | [(coeff, id)] when QQ.equal coeff QQ.one -> Some id
      | _ -> None
    in
    match Env.sd_term_of_id env id with
    | Mul (x, y) ->
      begin match id_of_vec x, id_of_vec y with
        | Some x, Some y ->
          add_coeff_bounds id x y;
          add_coeff_bounds id y x;
        | _, _ -> ()
      end
    | _ -> ()
  done;

  logf ~level:`trace "After strengthen: %a" pp property;

  property

let of_atoms ark ?integrity:(integrity=(fun _ -> ())) atoms =
  let env = Env.mk_empty ark in
  let register_terms atom =
    match Interpretation.destruct_atom ark atom with
    | `Comparison (_, x, y) ->
      ignore (Env.vec_of_term env x);
      ignore (Env.vec_of_term env y)
    | `Literal (_, _) -> assert false
  in
  List.iter register_terms atoms;
  let int_dim = Env.int_dim env in
  let real_dim = Env.real_dim env in
  let abstract =
    Abstract0.of_lincons_array
      (get_manager ())
      int_dim
      real_dim
      (Array.of_list (List.map (lincons_of_atom env) atoms))
  in
  strengthen ~integrity { env; abstract; int_dim; real_dim }

let common_env property property' =
  let ark = Env.ark property.env in
  let env = Env.mk_empty ark in
  let register_terms atom =
    match Interpretation.destruct_atom ark atom with
    | `Comparison (_, x, y) ->
      ignore (Env.vec_of_term env x);
      ignore (Env.vec_of_term env y);
    | `Literal (_, _) -> assert false
  in
  let atoms = to_atoms property in
  let atoms' = to_atoms property' in
  List.iter register_terms atoms;
  List.iter register_terms atoms';
  let int_dim = Env.int_dim env in
  let real_dim = Env.real_dim env in
  let abstract =
    Abstract0.of_lincons_array
      (get_manager ())
      int_dim
      real_dim
      (Array.of_list (List.map (lincons_of_atom env) atoms))
  in
  let abstract' =
    Abstract0.of_lincons_array
      (get_manager ())
      int_dim
      real_dim
      (Array.of_list (List.map (lincons_of_atom env) atoms'))
  in
  ({ env = env; abstract = abstract; int_dim; real_dim },
   { env = env; abstract = abstract'; int_dim; real_dim })

let join ?integrity:(integrity=(fun _ -> ())) property property' =
  if is_bottom property then property'
  else if is_bottom property' then property
  else
    let (property, property') = common_env property property' in
    let property = strengthen ~integrity property in
    let property' = strengthen ~integrity property' in
    update_env property; (* strengthening property' may add dimensions to the
                            common environment -- add those dimensions to
                            property *)
    { env = property.env;
      int_dim = property.int_dim;
      real_dim = property.real_dim;
      abstract =
        Abstract0.join (get_manager ()) property.abstract property'.abstract }

let equal property property' =
  let (property, property') = common_env property property' in
  let property = strengthen property in
  let property' = strengthen property' in
  Abstract0.is_eq (get_manager ()) property.abstract property'.abstract

(* Remove dimensions from an abstract value so that it has the specified
   number of integer and real dimensions n*)
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
    logf "Remove %d int, %d real: %a" remove_int remove_real
      (ApakEnum.pp_print_enum Format.pp_print_int) (BatArray.enum remove);
    assert (remove_int + remove_real = (Array.length remove));
    Abstract0.remove_dimensions
      (get_manager ())
      abstract
      { dim = remove;
        intdim = remove_int;
        realdim = remove_real }
  else
    abstract


let exists
    ?integrity:(integrity=(fun _ -> ()))
    ?subterm:(subterm=(fun _ -> true))
    p
    property =

  let ark = Env.ark property.env in
  let env = property.env in

  (* Orient equalities as rewrite rules to eliminate variables that should be
     projected out of the formula *)
  let rewrite_map =
    let keep id =
      id = Env.const_id || match Env.sd_term_of_id property.env id with
      | App (symbol, []) -> p symbol && subterm symbol
      | _ -> false (* to do: should allow terms containing only non-projected
                      symbols that are allowed as subterms *)
    in
    List.fold_left
      (fun map (id, rhs) ->
         match Env.sd_term_of_id env id with
         | App (symbol, []) ->
           let rhs_term = Env.term_of_vec env rhs in
           logf ~level:`info "Found rewrite: %a --> %a"
             (pp_symbol ark) symbol
             (Term.pp ark) rhs_term;
           Symbol.Map.add symbol rhs_term map
         | _ -> map)
      Symbol.Map.empty
      (Linear.orient keep (affine_hull property))
  in
  let rewrite =
    substitute_const
      ark
      (fun symbol ->
         try Symbol.Map.find symbol rewrite_map
         with Not_found -> mk_const ark symbol)
  in

  let forget = ref [] in
  let substitution = ref [] in
  let new_env = Env.mk_empty ark in
  let symbol_of id =
    match Env.sd_term_of_id env id with
    | App (symbol, []) -> Some symbol
    | _ -> None
  in
  for id = 0 to Env.dim env - 1 do
    let dim = Env.dim_of_id env id in
    match symbol_of id with
    | Some symbol ->
      begin
        if p symbol then
          let rewrite_vec = Env.vec_of_term new_env (mk_const ark symbol) in
          substitution := (dim, rewrite_vec)::(!substitution)
        else
          forget := dim::(!forget);
      end
    | None ->
      let term = Env.term_of_id env id in
      let term_rewrite = rewrite term in
      if Symbol.Set.for_all (fun x -> p x && subterm x) (symbols term_rewrite) then

        (* Add integrity constraint for term = term_rewrite *)
        let precondition =
          Symbol.Set.enum (symbols term)
          |> BatEnum.filter_map (fun x ->
              if Symbol.Map.mem x rewrite_map then
                Some (mk_eq ark (mk_const ark x) (Symbol.Map.find x rewrite_map))
              else
                None)
          |> BatList.of_enum
          |> mk_and ark
        in
        integrity (mk_or ark [mk_not ark precondition;
                              mk_eq ark term term_rewrite]);

        let rewrite_vec = Env.vec_of_term new_env term_rewrite in
        substitution := (dim, rewrite_vec)::(!substitution)
      else
        forget := dim::(!forget)
  done;

  let abstract =
    Abstract0.forget_array
      (get_manager ())
      property.abstract
      (Array.of_list (List.rev (!forget)))
      false
  in

  (* Ensure abstract has enough dimensions to be able to interpret the
     substitution.  The substituion is interpreted within an implicit
     ("virtual") environment. *)
  let virtual_int_dim =
    max (Env.int_dim env) (Env.int_dim new_env)
  in
  let virtual_dim_of_id id =
    let open Env in
    match type_of_id new_env id with
    | `TyInt -> ArkUtil.search id new_env.int_dim
    | `TyReal -> virtual_int_dim + (ArkUtil.search id new_env.real_dim)
  in
  let virtual_linexpr_of_vec vec =
    let mk (coeff, id) =
      (coeff_of_qq coeff, virtual_dim_of_id id)
    in
    let (const_coeff, rest) = V.pivot Env.const_id vec in
    Linexpr0.of_list None
      (BatList.of_enum (BatEnum.map mk (V.enum rest)))
      (Some (coeff_of_qq const_coeff))
  in

  let abstract =
    let int_dims = Env.int_dim env in
    let real_dims = Env.real_dim env in
    let added_int = max 0 ((Env.int_dim new_env) - int_dims) in
    let added_real = max 0 ((Env.real_dim new_env) - real_dims) in
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

  Log.logf ~level:`trace "Env (%d): %a"
    (List.length (!substitution))
    Env.pp new_env;
  List.iter (fun (dim, replacement) ->
      Log.logf ~level:`trace "Replace %a => %a"
        (Term.pp ark) (Env.term_of_id env (Env.id_of_dim env dim))
        (pp_vector new_env) replacement)
    (!substitution);

  let abstract =
    Abstract0.substitute_linexpr_array
      (get_manager ())
      abstract
      (BatArray.of_list (List.map fst (!substitution)))
      (BatArray.of_list (List.map (virtual_linexpr_of_vec % snd) (!substitution)))
      None
  in

  (* Remove extra dimensions *)
  let abstract =
    apron_set_dimensions
      (Env.int_dim new_env)
      (Env.real_dim new_env)
      abstract
  in
  let result =
    { env = new_env;
      int_dim = Env.int_dim new_env;
      real_dim = Env.real_dim new_env;
      abstract = abstract }
  in
  logf "Projection result: %a" pp result;
  result

let widen property property' =
  let ark = Env.ark property.env in
  let widen_env = Env.mk_empty ark in
  for id = 0 to (Env.dim property.env) - 1 do
    let term = Env.term_of_id property.env id in
    if Env.mem_term property'.env term then
      ignore (Env.vec_of_term widen_env term)
  done;

  (* Project onto intersected environment *)
  let project property =
    let forget = ref [] in
    let substitution = ref [] in
    for id = 0 to (Env.dim property.env) - 1 do
      let term = Env.term_of_id property.env id in
      let dim = Env.dim_of_id property.env id in
      if Env.mem_term widen_env term then
        substitution := (dim, Env.vec_of_term widen_env term)::(!substitution)
      else
        forget := dim::(!forget)
    done;
    let abstract =
      Abstract0.forget_array
        (get_manager ())
        property.abstract
        (Array.of_list (List.rev (!forget)))
        false
    in
    let abstract =
      Abstract0.substitute_linexpr_array
        (get_manager ())
        abstract
        (BatArray.of_list (List.map fst (!substitution)))
        (BatArray.of_list
           (List.map (Env.linexpr_of_vec widen_env % snd) (!substitution)))
        None
    in
    apron_set_dimensions
      (Env.int_dim widen_env)
      (Env.real_dim widen_env)
      abstract
  in
  let abstract = project property in
  let abstract' = project property' in
  { env = widen_env;
    int_dim = Env.int_dim widen_env;
    real_dim = Env.real_dim widen_env;
    abstract = Abstract0.widening (get_manager ()) abstract abstract' }

let farkas_equalities property =
  let open Lincons0 in
  let constraints =
    BatArray.enum (Abstract0.to_lincons_array (get_manager ()) property.abstract)
    |> BatEnum.filter_map (fun lcons ->
        match lcons.typ with
        | EQ -> Some lcons.linexpr0
        | _ -> None)
    |> BatArray.of_enum
  in
  let nb_columns =
    let dim = Abstract0.dimension (get_manager ()) property.abstract in
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
          mk_real (Env.ark property.env) QQ.one
        else
          Env.term_of_id property.env id
      in
      (term, column))
    columns
  |> Array.to_list

let symbolic_bounds cube symbol =
  let ark = Env.ark cube.env in
  let vec = Env.vec_of_term ~register:false cube.env (mk_const ark symbol) in
  match BatList.of_enum (V.enum vec) with
  | [(coeff, id)] ->
    assert (QQ.equal coeff QQ.one);

    let constraints =
      Abstract0.to_lincons_array (get_manager ()) cube.abstract
    in
    BatEnum.fold (fun (lower, upper) lincons ->
        let open Lincons0 in
        let vec = Env.vec_of_linexpr cube.env lincons.linexpr0 in
        let (a, t) = V.pivot id vec in
        if QQ.equal a QQ.zero then
          (lower, upper)
        else
          let bound =
            V.scalar_mul (QQ.negate (QQ.inverse a)) t
            |> Env.term_of_vec cube.env
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
