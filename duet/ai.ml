(** Abstract interpretation utilities, and an interface to APRON for numerical
    domains *)
open Core
open Srk
open Apak
open Apron

type abstract_domain = Box | Octagon | Polyhedron

(* magic is an uninhabited type that is used as a parameter to Abstract0.t and
   Manager.t.  We always coerce managers and abstract values to their magical
   counterparts so that the type stays the same even if the abstract domain
   changes.  *)
type magic
type abstract0 = magic Abstract0.t
type manager = magic Manager.t

(* Default abstract domain *)
let domain = ref Box

let is_relational_domain () = match !domain with
  | Box -> false
  | Octagon | Polyhedron -> true

let man : (manager option) ref = ref None
let get_man () = match !man with
  | Some m -> m
  | None ->
    let m = match !domain with
      | Box -> Box.manager_of_box (Box.manager_alloc ())
      | Octagon -> Oct.manager_of_oct (Oct.manager_alloc ())
      | Polyhedron -> Polka.manager_of_polka (Polka.manager_alloc_loose ())
    in
    man := Some m;
    m

let _ =
  let go s =
    man := None;
    domain := match s with
      | "box" -> Box
      | "oct" -> Octagon
      | "polka" -> Polyhedron
      | _ -> failwith ("The abstract domain `" ^ s ^ " ' is not recognized")
  in
  CmdLine.register_config
    ("-domain", Arg.String go, " Set abstract domain (box,oct,polka)")

type absbool = Yes | No | Bottom | Top

module type MinInterpretation = sig
  include Sig.Semilattice.S
  val widen : t -> t -> t
  val bottom : t
  val name : string
  val transfer : def -> t -> t
end

module type Domain = sig
  type t
  val pp : Format.formatter -> t -> unit
  val project : t -> AP.Set.t -> t
  val inject : t -> AP.Set.t -> t
  val cyl : t -> AP.Set.t -> t
  val rename : t -> (ap * ap) list -> t
  val equal : t -> t -> bool
  val join : t -> t -> t
  val widen : t -> t -> t
  val meet : t -> t -> t
  val bottom : AP.Set.t -> t
  val top : AP.Set.t -> t
  val is_bottom : t -> bool
end

module type Interpretation = sig
  include Domain
  val transfer : def -> t -> t
  val assert_true : bexpr -> t -> bool
  val assert_memsafe : aexpr -> t -> bool
  val name : string
end

type 'a ptr_value =
  { ptr_val : 'a;
    ptr_pos : 'a;
    ptr_width : 'a }

type 'a value =
  | VInt of 'a
  | VPointer of ('a ptr_value)
  | VDynamic

module ApronInterpretation = struct
  open Dim

  module Env = struct
    include Putil.MonoMap.Make(AP)(struct
        type t = Dim.t value
        let pp formatter = function
          | VInt x -> Format.fprintf formatter "Int[%d]" x
          | VPointer p ->
            Format.fprintf formatter "Ptr[%d,%d,%d]"
              p.ptr_val p.ptr_pos p.ptr_width
          | VDynamic -> Format.pp_print_string formatter "Dyn"
      end)
    let delete k =
      let shift d = if d > k then d - 1 else d in
      let f = function
        | VInt d -> VInt (shift d)
        | VPointer p -> VPointer { ptr_val = shift p.ptr_val;
                                   ptr_pos = shift p.ptr_pos;
                                   ptr_width = shift p.ptr_width }
        | VDynamic -> VDynamic
      in
      map f
  end

  type t =
    { env : Env.t;
      value : abstract0 }

  (* Constants *)
  let infty = Scalar.of_infty 1
  let neg_infty = Scalar.of_infty (-1)
  let havoc_int = Texpr0.Cst (Coeff.Interval Interval.top)
  let havoc_bool = Texpr0.Cst (Coeff.i_of_int 0 1)
  let havoc_positive_int =
    Texpr0.Cst (Coeff.i_of_scalar (Scalar.of_int 1) infty)
  let texpr_zero = Texpr0.Cst (Coeff.s_of_int 0)
  let texpr_one = Texpr0.Cst (Coeff.s_of_int 1)

  let is_bottom v = Abstract0.is_bottom (get_man()) v.value
  let is_top v = Abstract0.is_top (get_man()) v.value

  let get_domain av =
    let f k _ set = AP.Set.add k set in
    Env.fold f av.env AP.Set.empty

  let format_coeff formatter coeff =
    let format_scalar formatter s =
      Format.pp_print_string formatter (Scalar.to_string s)
    in
    match coeff with
    | Coeff.Scalar s -> format_scalar formatter s
    | Coeff.Interval ivl ->
      Format.fprintf formatter "[@[%a,%a@]]"
        format_scalar ivl.Interval.inf
        format_scalar ivl.Interval.sup

  module DimMap = Putil.PInt.Map

  let is_positive x = match Coeff.reduce x with
    | Coeff.Scalar x -> Scalar.cmp_int x 0 > 0
    | Coeff.Interval _ -> true

  let pp formatter av =
    let lincons = Abstract0.to_lincons_array (get_man()) av.value in
    let add_to_env ap value env = match value with
      | VInt d -> DimMap.add d (AP.show ap) env
      | VPointer ptr ->
        DimMap.add ptr.ptr_val (AP.show ap)
          (DimMap.add ptr.ptr_pos ("pos@" ^ (AP.show ap))
             (DimMap.add ptr.ptr_width ("width@" ^ (AP.show ap)) env))
      | VDynamic -> env
    in
    let env = Env.fold add_to_env av.env DimMap.empty in
    let domain =
      Env.fold (fun ap _ -> AP.Set.add ap) av.env AP.Set.empty
    in
    let format_linexpr linexpr =
      Linexpr0.print (fun d -> DimMap.find d env) linexpr
    in
    let pp_elt formatter cons =
      format_linexpr formatter cons.Lincons0.linexpr0;
      Format.fprintf formatter " %s 0"
        (Lincons0.string_of_typ cons.Lincons0.typ)
    in
    AP.Set.pp formatter domain;
    Format.pp_print_string formatter ". ";
    if is_top av then
      Format.pp_print_string formatter "T"
    else if is_bottom av then
      Format.pp_print_string formatter "_|_"
    else
      SrkUtil.pp_print_enum
        ~pp_sep:(fun formatter () -> Format.fprintf formatter "@ && ")
        pp_elt
        formatter
        (BatArray.enum lincons)

  (* Create a new pointer value, where ptr_val, ptr_pos, and ptr_width are
     new dimension, starting with n *)
  let ptr_at n =
    { ptr_val = n;
      ptr_pos = n + 1;
      ptr_width = n + 2 }

  let project av aps =
    let add_ap ap value (forget_dim, env) =
      if AP.Set.mem ap aps then (forget_dim, Env.add ap value env) else
        begin match value with
          | VInt dim -> (dim::forget_dim, env)
          | VPointer p ->
            (p.ptr_val::(p.ptr_pos::(p.ptr_width::forget_dim)), env)
          | VDynamic -> (forget_dim, env)
        end
    in
    let (forget_dim, env) = Env.fold add_ap av.env ([], Env.empty) in
    let forget_dim_array = Array.of_list forget_dim in
    let rename i =
      let rec go j =
        if j >= Array.length forget_dim_array then i
        else if forget_dim_array.(j) < i then go (j+1) - 1
        else i
      in
      go 0
    in
    let rename_env x value env = match value with
      | VInt dim -> Env.add x (VInt (rename dim)) env
      | VPointer p ->
        let p_rename =
          { ptr_val = rename p.ptr_val;
            ptr_pos = rename p.ptr_pos;
            ptr_width = rename p.ptr_width }
        in
        Env.add x (VPointer p_rename) env
      | VDynamic -> Env.add x VDynamic env
    in
    Array.sort Pervasives.compare forget_dim_array;
    let value =
      Abstract0.remove_dimensions (get_man()) av.value
        { dim = forget_dim_array;
          intdim = Array.length forget_dim_array;
          realdim = 0 }
    in
    { env = Env.fold rename_env env Env.empty;
      value = value }

  let get_dimension av = (Abstract0.dimension (get_man()) av.value).intd

  let add_dimensions num_av add =
    if add = 0 then num_av else
      let current_dim = (Abstract0.dimension (get_man()) num_av).intd in
      Abstract0.add_dimensions (get_man()) num_av
        { dim = Array.make add current_dim;
          intdim = add;
          realdim = 0 }
        false

  let inject av aps =
    let add_ap ap av = if Env.mem ap av.env then av else
        match resolve_type (AP.get_type ap) with
        | Core.Int _ ->
          { env = Env.add ap (VInt (get_dimension av)) av.env;
            value = add_dimensions av.value 1 }
        | Core.Pointer _ ->
          let vptr = ptr_at (get_dimension av) in
          { env = Env.add ap (VPointer vptr) av.env;
            value = add_dimensions av.value 3 }
        | _ -> { av with env = Env.add ap VDynamic av.env }
    in
    try AP.Set.fold add_ap aps av
    with Manager.Error exc -> failwith ("Inject error: " ^ exc.Manager.msg)

  (* Look up an access path in an abstract value *)
  let lookup x av =
    try Env.find x av.env
    with Not_found ->
      Format.printf "Missing dimension %a in %a"
        AP.pp x
        pp av;
      flush stdout;
      flush stderr;
      assert false

  let cyl av aps =
    let add_ap ap dimensions = match lookup ap av with
      | VInt dim -> dim::dimensions
      | VPointer p ->
        p.ptr_val::(p.ptr_pos::(p.ptr_width::dimensions))
      | VDynamic -> dimensions
    in
    let forget_dimensions = Array.of_list (AP.Set.fold add_ap aps []) in
    let value =
      Abstract0.forget_array (get_man()) av.value forget_dimensions false
    in
    { av with value = value }

  let equal av0 av1 =
    Env.equal (=) av0.env av1.env
    && Abstract0.is_eq (get_man()) av0.value av1.value

  let rename av rename =
    let map =
      List.fold_right (fun (x,y) -> AP.Map.add x y) rename AP.Map.empty
    in
    let lookup x =
      try AP.Map.find x map
      with Not_found -> x
    in
    let add k vtyp map = Env.add (lookup k) vtyp map in
    { av with env = Env.fold add av.env Env.empty }

  let bottom aps =
    inject
      { env = Env.empty; value = Abstract0.bottom (get_man()) 0 0 }
      aps
  let top aps =
    inject
      { env = Env.empty; value = Abstract0.top (get_man()) 0 0 }
      aps

  (* Compute a common environment for the abstract values x and y, and then
     apply the function f to the numerical abstract values for x and y in the
     common environment *)
  let common_env f x y =
    let get_aps z =
      Env.fold (fun k v s -> AP.Set.add k s) z.env AP.Set.empty
    in
    let aps = AP.Set.union (get_aps x) (get_aps y) in
    let x = inject x aps in
    let y = inject y aps in
    let x_dim = ref (get_dimension x) in
    let y_dim = ref (get_dimension y) in
    let alloc_dim z_dim num =
      let start = !z_dim in
      z_dim := start + num;
      start
    in
    let ptr_rename var p0 p1 (rename, env) =
      let rename =
        (p0.ptr_val,p1.ptr_val)::
        ((p0.ptr_pos,p1.ptr_pos)::
         ((p0.ptr_width,p1.ptr_width)::rename))
      in
      (rename, Env.add var (VPointer p0) env)
    in
    let int_rename var d0 d1 (rename, env) =
      ((d0,d1)::rename, Env.add var (VInt d0) env)
    in
    let dyn_rename var (rename, env) = (rename, Env.add var VDynamic env) in
    let add var (rename, env) = match lookup var x, lookup var y with
      | (VInt d0, VInt d1) -> int_rename var d0 d1 (rename, env)
      | (VPointer p0, VPointer p1) -> ptr_rename var p0 p1 (rename, env)
      | (VDynamic, VDynamic) -> dyn_rename var (rename, env)
      | (VDynamic, VInt d1) ->
        int_rename var (alloc_dim x_dim 1) d1 (rename, env)
      | (VInt d0, VDynamic) ->
        int_rename var d0 (alloc_dim y_dim 1) (rename, env)
      | (VDynamic, VPointer p1) ->
        let p0 = ptr_at (alloc_dim x_dim 3) in
        ptr_rename var p0 p1 (rename, env)
      | (VPointer p0, VDynamic) ->
        ptr_rename var p0 (ptr_at (alloc_dim y_dim 3)) (rename, env)
      | (VPointer p0, VInt d1) ->
        let start = alloc_dim y_dim 2 in
        let p1 =
          { ptr_val = d1;
            ptr_pos = start;
            ptr_width = start + 1 }
        in
        ptr_rename var p0 p1 (rename, env)
      | (VInt d0, VPointer p1) ->
        let start = alloc_dim x_dim 2 in
        let p0 =
          { ptr_val = d0;
            ptr_pos = start;
            ptr_width = start + 1 }
        in
        ptr_rename var p0 p1 (rename, env)
    in
    let (rename, env) = AP.Set.fold add aps ([], Env.empty) in
    let perm = Array.of_list rename in
    Array.sort (fun x y -> Pervasives.compare (snd x) (snd y)) perm;

    let x_val = add_dimensions x.value (!x_dim - (get_dimension x)) in
    let y_val = add_dimensions y.value (!y_dim - (get_dimension y)) in
    let y_val =
      Abstract0.permute_dimensions (get_man()) y_val (Array.map fst perm)
    in
    { env = env;
      value = f x_val y_val }

  let join x y =
    try Log.time "join" (common_env (Abstract0.join (get_man())) x) y
    with Manager.Error exc ->
      failwith ("Join error: " ^ exc.Manager.msg)
  let meet x y =
    try Log.time "meet" (common_env (Abstract0.meet (get_man())) x) y
    with Manager.Error exc ->
      failwith ("Meet error: " ^ exc.Manager.msg)
  let widen x y =
    try Log.time "widen" (common_env (Abstract0.widening (get_man())) x) y
    with Manager.Error exc ->
      failwith ("Widen error: " ^ exc.Manager.msg)

  let assign_int lhs rhs av =
    let rhs = Texpr0.of_expr rhs in
    match lookup lhs av with
    | VInt dim ->
      { av with
        value = Abstract0.assign_texpr (get_man()) av.value dim rhs None }
    | VPointer ptr ->
      let dim = ptr.ptr_val in
      let value =
        Abstract0.assign_texpr (get_man()) av.value dim rhs None
      in
      let value =
        Abstract0.remove_dimensions (get_man()) value
          { dim = [| ptr.ptr_pos; ptr.ptr_width |];
            intdim = 2;
            realdim = 0 }
      in
      let env =
        Env.delete ptr.ptr_width
          (Env.delete ptr.ptr_pos (Env.add lhs (VInt dim) av.env))
      in
      { env = env;
        value = value }
    | VDynamic ->
      let dim = get_dimension av in
      let value = add_dimensions av.value 1 in
      let env = Env.add lhs (VInt dim) av.env in
      { env = env;
        value = Abstract0.assign_texpr (get_man()) value dim rhs None }

  let assign_ptr lhs rhs av =
    let (p, av) = match lookup lhs av with
      | VInt dim ->
        let pos_dim = get_dimension av in
        let value = add_dimensions av.value 2 in
        let p =
          { ptr_val = dim;
            ptr_pos = pos_dim;
            ptr_width = pos_dim + 1 }
        in
        let env = Env.add lhs (VPointer p) av.env in
        (p, {env = env; value = value })
      | VPointer p -> (p, av)
      | VDynamic ->
        let p = ptr_at (get_dimension av) in
        let value = add_dimensions av.value 3 in
        let env = Env.add lhs (VPointer p) av.env in
        (p, {env = env; value = value })
    in
    let value =
      Abstract0.assign_texpr_array (get_man()) av.value
        [| p.ptr_val; p.ptr_pos; p.ptr_width |]
        [| Texpr0.of_expr rhs.ptr_val;
           Texpr0.of_expr rhs.ptr_pos;
           Texpr0.of_expr rhs.ptr_width |]
        None
    in
    { av with value = value }

  let assign lhs rhs av =
    try begin match rhs with
      | VInt x -> assign_int lhs x av
      | VPointer p -> assign_ptr lhs p av
      | VDynamic -> cyl av (AP.Set.singleton lhs)
    end with Manager.Error exc -> failwith ("Assign error: " ^ exc.Manager.msg)

  let int_binop op left right =
    let normal_op op =
      Texpr0.Binop (op, left, right, Texpr0.Int, Texpr0.Down)
    in
    match op with
    | Add -> normal_op Texpr0.Add
    | Minus -> normal_op Texpr0.Sub
    | Mult -> normal_op Texpr0.Mul
    | Div -> normal_op Texpr0.Div
    | Mod -> normal_op Texpr0.Mod
    | ShiftL | ShiftR | BXor | BAnd | BOr -> havoc_int

  let vint_of_value = function
    | VInt x -> x
    | VPointer p -> p.ptr_val
    | VDynamic -> havoc_int


  let apron_binop op left right = match left, op, right with
    | (VInt left, op, VInt right) ->
      VInt (int_binop op left right)
    | (VPointer ptr, Add, VInt offset)
    | (VInt offset, Add, VPointer ptr) ->
      let p =
        { ptr_val = int_binop Add ptr.ptr_val offset;
          ptr_pos = int_binop Add ptr.ptr_pos offset;
          ptr_width = ptr.ptr_width }
      in
      VPointer p
    | (VPointer ptr, Minus, VInt offset) ->
      let p =
        { ptr_val = int_binop Minus ptr.ptr_val offset;
          ptr_pos = int_binop Minus ptr.ptr_pos offset;
          ptr_width = ptr.ptr_width }
      in
      VPointer p
    | (VInt offset, Minus, VPointer ptr) ->
      let p =
        { ptr_val = int_binop Minus offset ptr.ptr_val;
          ptr_pos = int_binop Minus offset ptr.ptr_pos;
          ptr_width = ptr.ptr_width }
      in
      VPointer p
    | (VPointer left, op, VInt right) ->
      VInt (int_binop op left.ptr_val right)
    | (VInt left, op, VPointer right) ->
      VInt (int_binop op left right.ptr_val)
    | (VPointer left, op, VPointer right) ->
      VInt (int_binop op left.ptr_val right.ptr_val)
    | (VInt left, op, VDynamic) ->
      VInt (int_binop op left havoc_int)
    | (VDynamic, op, VInt right) ->
      VInt (int_binop op havoc_int right)
    | (VPointer left, op, VDynamic) ->
      VInt (int_binop op left.ptr_val havoc_int)
    | (VDynamic, op, VPointer right) ->
      VInt (int_binop op havoc_int right.ptr_val)
    | (VDynamic, op, VDynamic) -> VDynamic

  let rec apron_expr av expr =
    let f = function
      | OHavoc typ ->
        begin match resolve_type typ with
          | Int _ -> VInt havoc_int
          | Pointer _ ->
            VPointer { ptr_val = havoc_int;
                       ptr_pos = havoc_int;
                       ptr_width = havoc_int }
          | Dynamic -> VDynamic
          | _ -> Log.fatalf "Havoc with a non-integer type: %a" pp_typ typ
        end
      | OConstant (CInt (c, _)) -> VInt (Texpr0.Cst (Coeff.s_of_int c))
      | OConstant (CFloat (c, _)) -> VInt (Texpr0.Cst (Coeff.s_of_float c))
      | OConstant (CChar c) ->
        VInt (Texpr0.Cst (Coeff.s_of_int (int_of_char c)))
      | OConstant (CString str) ->
        let width = Texpr0.Cst (Coeff.s_of_int (String.length str)) in
        VPointer { ptr_val = havoc_positive_int;
                   ptr_pos = texpr_zero;
                   ptr_width = width }
      | OAccessPath ap -> begin match lookup ap av with
          | VInt d -> VInt (Texpr0.Dim d)
          | VPointer p -> VPointer { ptr_val = Texpr0.Dim p.ptr_val;
                                     ptr_pos = Texpr0.Dim p.ptr_pos;
                                     ptr_width = Texpr0.Dim p.ptr_width }
          | VDynamic -> VDynamic
        end
      | OCast (typ, x) -> x (* todo *)
      | OBinaryOp (left, op, right, _) -> apron_binop op left right
      | OUnaryOp (Neg, VInt expr, _) ->
        VInt (Texpr0.Unop (Texpr0.Neg, expr, Texpr0.Int, Texpr0.Down))
      | OUnaryOp (Neg, VPointer expr, _) ->
        VInt (Texpr0.Unop (Texpr0.Neg, expr.ptr_val, Texpr0.Int, Texpr0.Down))
      | OUnaryOp (BNot, _, _) -> VInt havoc_int
      | OBoolExpr expr -> VInt havoc_bool (* todo *)
      | OAddrOf (Variable (v, offset)) ->
        let pos = match offset with
          | OffsetFixed x -> Texpr0.Cst (Coeff.s_of_int x)
          | OffsetUnknown -> havoc_int
        in
        let width = typ_width (Varinfo.get_type v) in
        let p =
          { ptr_val = havoc_positive_int;
            ptr_pos = pos;
            ptr_width = Texpr0.Cst (Coeff.s_of_int width)}
        in
        VPointer p
      | OAddrOf _ -> (* todo *)
        let p =
          { ptr_val = havoc_int;
            ptr_pos = havoc_int;
            ptr_width = havoc_int }
        in
        VPointer p
      | _ -> VDynamic
    in
    Aexpr.fold f expr

  (* Translate an atom to APRON's representation: an (expression, constraint
     type) pair *)
  let apron_atom pred a b =
    let sub = apron_binop Minus in
    let one = VInt (Texpr0.Cst (Coeff.s_of_int 1)) in
    let texpr x = Texpr0.of_expr (vint_of_value x) in
    match pred with
    | Eq -> (texpr (sub a b), Tcons0.EQ)
    | Ne -> (texpr (sub a b), Tcons0.DISEQ)
    | Le -> (texpr (sub b a), Tcons0.SUPEQ)
    | Lt -> (texpr (sub (sub b a) one), Tcons0.SUPEQ)

  let assert_memsafe expr av = match apron_expr av expr with
    | VDynamic | VInt _ -> false
    | VPointer p ->
      let sub a b = int_binop Minus a b in
      let one = Texpr0.Cst (Coeff.s_of_int 1) in
      let texpr = Texpr0.of_expr in
      let lt a b =
        Tcons0.make (texpr (sub (sub b a) one)) Tcons0.SUPEQ
      in
      let sat cons = Abstract0.sat_tcons (get_man()) av.value cons in
      sat (lt (Texpr0.Cst (Coeff.s_of_int 0)) p.ptr_val)
      && sat (lt p.ptr_pos p.ptr_width)
      && sat (Tcons0.make (texpr p.ptr_pos) Tcons0.SUPEQ)

  (** Return true iff expr is definitely true in av. *)
  let rec assert_true bexpr av =
    match bexpr with
    | And (a, b) -> (assert_true a av) && (assert_true b av)
    | Or (a, b) ->
      (assert_true a av)
      || (assert_true b (interp_bool (Bexpr.negate a) av))
    | Atom (Ne, a, b) ->
      (assert_true (Atom (Lt, a, b)) av)
      || (assert_true (Bexpr.gt a b) av)
    | Atom (pred, a, b) ->
      let (expr, typ) =
        apron_atom pred (apron_expr av a) (apron_expr av b)
      in
      Abstract0.sat_tcons (get_man()) av.value (Tcons0.make expr typ)

  (* Given an arbitrary Boolean constraint and an abstract value, compute the
     meet of the constraint and the value *)
  and interp_bool expr av =
    match expr with
    | And (a, b) -> interp_bool b (interp_bool a av)
    | Or (a, b) -> join (interp_bool a av) (interp_bool b av)

    (* Apron handles disequality inaccurately.  This seems to be a reasonable
       replacement *)
    | Atom (Ne, a, b) ->
      join
        (interp_bool (Atom (Lt, a, b)) av)
        (interp_bool (Atom (Lt, b, a)) av)
    | Atom (pred, a, b) ->
      if Bexpr.equal expr Bexpr.ktrue then av else begin
        let (expr, typ) =
          apron_atom pred (apron_expr av a) (apron_expr av b)
        in
        let value =
          Abstract0.meet_tcons_array
            (get_man())
            av.value
            [| Tcons0.make expr typ |]
        in
        { av with value = value }
      end

  (** Widen, but preserve variable strict inequalities (i.e., if a < b in x
      and y, then a < b in (widen_preserve_leq x y). *)
  let widen_preserve_leq x y =
    let w = widen x y in
    let f a b value =
      let texpr = (* a - b - 1 *)
        Texpr0.of_expr
          (int_binop Minus
             (int_binop Minus (Texpr0.Dim a) (Texpr0.Dim b))
             (Texpr0.Cst (Coeff.s_of_int 1)))
      in
      let tcons = Tcons0.make texpr Tcons0.SUPEQ in
      if (Abstract0.sat_tcons (get_man()) x.value tcons
          && Abstract0.sat_tcons (get_man()) y.value tcons
          && not (Abstract0.sat_tcons (get_man()) value tcons))
      then Abstract0.meet_tcons_array (get_man()) value [| tcons |]
      else value
    in
    let value =
      let g _ d1 value =
        let h _ d2 value =
          match d1,d2 with
          | VInt a, VInt b -> f a b value
          | _,_ -> value
        in
        Env.fold h w.env value
      in
      Env.fold g w.env w.value
    in
    { w with value = value }

  let assert_true bexpr av = assert_true (Bexpr.dnf bexpr) av
  let interp_bool bexpr av = interp_bool bexpr av

  (* Assign pointer a freshly allocated chunk of memory of the given size
     within the given abstract value.  If !CmdLine.fail_malloc is set, then
     alloc then the value that alloc assigns to ptr includes null. *)
  let alloc ptr size av =
    let lower =
      Scalar.of_int (if !CmdLine.fail_malloc then 0 else 1)
    in
    let rhs =
      { ptr_val = Texpr0.Cst (Coeff.i_of_scalar lower infty);
        ptr_pos = texpr_zero;
        ptr_width = vint_of_value size }
    in
    assign_ptr ptr rhs av

  (* Same as alloc, except alloc_safe never assigns null *)
  let alloc_safe ptr size av =
    let rhs =
      { ptr_val = havoc_positive_int;
        ptr_pos = texpr_zero;
        ptr_width = vint_of_value size }
    in
    assign_ptr ptr rhs av

  (* This is only safe for library calls - ie. no globals are modified *)
  let approx_call apset av =
    let f ap = assign_int ap havoc_int in
    AP.Set.fold f apset av

  (** Defines the abstract semantics of def as an abstract value
      transformer. *)
  let transfer def av =
    let av = inject av (AP.Set.union (Def.get_defs def) (Def.get_uses def)) in
    match def.dkind with
    | Assign (var, expr) -> assign (Variable var) (apron_expr av expr) av
    | Store (ap, expr) -> assign ap (apron_expr av expr) av
    | Assume expr -> interp_bool expr av

    (* Don't propagate erroneous values *)
    | Assert (expr, _) -> interp_bool expr av
    | AssertMemSafe (expr, _) -> begin match apron_expr av expr with
        | VDynamic | VInt _ -> av (* todo *)
        | VPointer p ->
          (* val > 0 && 0 <= pos < width *)
          let sub a b = int_binop Minus a b in
          let one = Texpr0.Cst (Coeff.s_of_int 1) in
          let texpr = Texpr0.of_expr in
          let lt a b =
            Tcons0.make (texpr (sub (sub b a) one)) Tcons0.SUPEQ
          in
          let constrain =
            [| lt (Texpr0.Cst (Coeff.s_of_int 0)) p.ptr_val;
               lt p.ptr_pos p.ptr_width;
               Tcons0.make (texpr p.ptr_pos) Tcons0.SUPEQ |]
          in
          let value =
            Abstract0.meet_tcons_array (get_man()) av.value constrain
          in
          { av with value = value  }
      end
    | Initial ->
      let set_init ap _ av = match AP.get_ctype ap with
        | Array (_, Some (_, size)) ->
          alloc_safe ap (VInt (Texpr0.Cst (Coeff.s_of_int size))) av
        | _ -> av
      in
      Env.fold set_init av.env av
    | Call _ -> approx_call (Def.get_defs def) av
    | Return _ -> av
    | Builtin (Alloc (ptr, size, AllocHeap)) ->
      alloc (Variable ptr) (apron_expr av size) av
    | Builtin (Alloc (ptr, size, AllocStack)) ->
      alloc_safe (Variable ptr) (apron_expr av size) av
    | Builtin (Free _) -> av (* todo *)
    | Builtin (Fork _) -> av
    | Builtin (Acquire _) | Builtin (Release _) -> av
    | Builtin AtomicBegin | Builtin AtomicEnd -> av
    | Builtin Exit -> bottom (get_domain av)

  module REnv = Putil.PInt.Map

  let build_renv env =
    let f v value renv = match value with
      | VInt dim -> REnv.add dim (AccessPath v) renv
      | VPointer _ | VDynamic -> renv
    in
    let renv = Env.fold f env REnv.empty in
    fun x -> try Some (REnv.find x renv) with Not_found -> None

  let int_of_scalar = function
    | Scalar.Mpqf qq ->
      let (num,den) = Mpqf.to_mpzf2 qq in
      let (num,den) = (Mpz.get_int num, Mpz.get_int den) in
      assert (den == 1);
      Some num
    | _ -> None

  let apron_expr renv texpr =
    let open Texpr0 in
    let open Coeff in
    let rec go = function
      |	Cst (Scalar s) -> begin match int_of_scalar s with
          | Some k -> Some (Aexpr.const_int k)
          | None -> None
        end
      | Cst (Interval _) -> None
      |	Dim d -> renv d
      |	Unop (op, expr, typ, round) ->
        begin match go expr with
          | None -> None
          | Some expr ->
            begin match op with
              | Neg -> Some (Aexpr.neg expr)
              | Cast -> None
              | Sqrt -> None
            end
        end
      |	Binop (op, left, right, typ, round) ->
        begin match go left, go right with
          | (None, _) | (_, None) -> None
          | (Some left, Some right) ->
            Some begin match op with
              | Add -> Aexpr.add left right
              | Sub -> Aexpr.sub left right
              | Mul -> Aexpr.mul left right
              | Div -> Aexpr.div left right
              | Mod -> Aexpr.modulo left right
              | Pow -> assert false
            end
        end
    in
    go (to_expr texpr)

  let tcons_bexpr renv tcons =
    let open Tcons0 in
    let zero = Aexpr.zero in
    match apron_expr renv tcons.texpr0 with
    | None -> None
    | Some expr ->
      match tcons.typ with
      | EQ -> Some (Atom (Eq, expr, zero))
      | SUPEQ -> Some (Bexpr.ge expr zero)
      | SUP -> Some (Bexpr.gt expr zero)
      | DISEQ -> Some (Atom (Ne, expr, zero))
      | EQMOD s -> begin match int_of_scalar s with
          | Some k ->
            Some (Atom (Eq, Aexpr.modulo expr (Aexpr.const_int k), zero))
          | None -> None
        end

  let bexpr_of_av av =
    let renv = build_renv av.env in
    let tcons = BatArray.enum (Abstract0.to_tcons_array (get_man()) av.value) in
    let conjuncts = BatEnum.filter_map (tcons_bexpr renv) tcons in
    BatEnum.fold (fun x y -> And (x, y)) Bexpr.ktrue conjuncts

  let name = "APRON"
end

(** Derived operations on interpretations *)
module IExtra (I : Interpretation) =
struct
  include I
  (** Evaluate a predicate in an abstract environment. *)
  let eval_pred pred value =
    if I.is_bottom value then Bottom
    else if I.assert_true pred value then Yes
    else if I.assert_true (Bexpr.negate pred) value then No
    else Top
end
