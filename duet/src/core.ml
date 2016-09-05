(** Core contains the core type definitions and conversion functions used by
    our internal representations, including the type [ap] of access paths and
    [expr] of expressions.  Further operations on expr can be found in
    [Expr]. *)
open Apak
open BatPervasives

(** Record containing the information of enumeration *)
type enuminfo = {
  enname : string;
  mutable enitems : (string * int) list
}

(** Concrete type (any type that is not a named type *)
type ctyp =
  | Void
  | Lock
  | Int       of int
  | Float     of int
  | Pointer   of typ
  | Array     of typ * int option 
  | Record    of recordinfo
  | Enum      of enuminfo
  | Func      of typ * typ list (** A function type consists of a return type
                                    and a list of parameter types. *)
  | Union     of recordinfo
  | Dynamic (** A default type for values that cannot be assigned a static
                type, or whose static type is misleading or uninformative *)
and typ =
  | Named     of string * ctyp ref (** A named type consists of a name and a
                                       reference to its underlying concrete
                                       type *)
  | Concrete  of ctyp

and field = {
  finame : string;
  fityp : typ;
  fioffset : int;
}

and recordinfo = {
  rname : string;
  rfields : field list;
  rkey : int; (* key required for duplicate structs etc.*)
}

module Compare_typ = struct
  type a = typ
  let compare = Pervasives.compare
end

(** Unary operations *)
type unop =
  | Neg
  | BNot
      deriving (Compare)

(** Binary operations *)
type binop =
  | Add
  | Minus
  | Mult
  | Div 
  | Mod 
  | ShiftL
  | ShiftR
  | BXor
  | BAnd
  | BOr
      deriving (Compare)

type pred =
  | Lt
  | Le
  | Eq
  | Ne
      deriving (Compare)

type visibility =
  | VzGlobal      (** Global variable *)
  | VzLocal       (** Local variable *)
  | VzThreadLocal (** Thread local variable (per-thread variable with global
                      scope) *)

let vz_is_shared = function
  | VzGlobal -> true
  | VzLocal | VzThreadLocal -> false

let vz_is_global = function
  | VzGlobal | VzThreadLocal -> true
  | VzLocal -> false

type varinfo = {
  mutable vname : string;
  mutable vid : int;
  mutable vsubscript : int; (** Variable subscript *)
  mutable vtyp : typ;
  mutable vviz : visibility;
  mutable vaddr_taken: bool;
}
module Compare_varinfo = struct
  type a = varinfo
  let compare x y = compare (x.vid, x.vsubscript) (y.vid, y.vsubscript)
end
module Eq_varinfo = struct
  type a = varinfo
  let eq x y =
    x.vid = y.vid && x.vsubscript = y.vsubscript
end
module Show_varinfo = Deriving_Show.Defaults(struct
    type a = varinfo
    let format formatter x =
      if x.vsubscript = 0 then Format.pp_print_string formatter x.vname
      else Format.fprintf formatter "%s<%d>" x.vname x.vsubscript
  end)
module Varinfo = struct
  include Putil.MakeCoreType(struct
      type t = varinfo deriving (Show,Compare)
      let format = Show_varinfo.format
      let show = Show_varinfo.show
      let compare = Compare_t.compare
      let hash x = Hashtbl.hash (x.vid, x.vsubscript)
      let equal x y = x.vid = y.vid && x.vsubscript = y.vsubscript
    end)

  let get_visibility v = v.vviz
  let is_global = vz_is_global % get_visibility
  let is_shared = vz_is_shared % get_visibility

  let addr_taken v = v.vaddr_taken
  let get_type v = v.vtyp
  let set_global v = v.vviz <- VzGlobal
  let subscript v ss = { v with vsubscript = ss }
  let get_subscript v = v.vsubscript

  let max_var_id = ref 0

  (** mk_global_var should not be called directly.  Prefer {!Ast.mk_local_var},
      {!Ast.mk_global_var}, {!CfgIr.mk_local_var}, and {!CfgIr.mk_global_var} *)
  let mk_global name typ =
    let id = !max_var_id in
    max_var_id := id + 1;
    { vname = name;
      vid   = id;
      vsubscript = 0;
      vtyp  = typ;
      vviz = VzGlobal;
      vaddr_taken = false }
  let mk_local name typ =
    let v = mk_global name typ in
    v.vviz <- VzLocal;
    v
  let mk_thread_local name typ =
    let v = mk_global name typ in
    v.vviz <- VzThreadLocal;
    v

  let clone v =
    let clone = mk_global v.vname v.vtyp in
    clone.vviz <- v.vviz;
    clone
end

type offset =
  | OffsetFixed of int
  | OffsetUnknown
      deriving (Functor, Compare, Eq)
module Offset = struct
  include Putil.MakeCoreType(struct
      type t = offset deriving (Compare)
      include Putil.MakeFmt(struct
          type a = t
          let format fmt = function
            | OffsetFixed x -> Format.pp_print_int fmt x
            | OffsetUnknown -> Format.pp_print_string fmt "Top"
        end)
      let hash = Hashtbl.hash
      let compare = Compare_t.compare
      let equal = (=)
    end)
  let add x y = match x,y with
    | (OffsetFixed x, OffsetFixed y) -> OffsetFixed (x + y)
    | _ -> OffsetUnknown
end

type var = varinfo * offset deriving (Compare, Eq)

(** Constants *)
type constant =
  | CInt          of int * int
  | CString       of string 
  | CChar         of char 
  | CFloat        of float * int
                       deriving (Compare)

(** Access paths *)
type ap =
  | Variable      of var
  | Deref         of expr

(** Boolean expressions (in negation normal form) *)
and bexpr =
  | Atom          of (pred * expr * expr)
  | And           of (bexpr * bexpr)
  | Or            of (bexpr * bexpr)

(** Expressions *)
and expr =
  | Havoc         of typ
  | Constant      of constant
  | Cast          of typ * expr
  | BinaryOp      of expr * binop * expr * typ
  | UnaryOp       of unop * expr * typ
  | AccessPath    of ap
  | BoolExpr      of bexpr
  | AddrOf        of ap
        deriving (Compare)

type alloc_target =
  | AllocHeap
  | AllocStack

(** Builtin definitions *)
type builtin =
  | Alloc of (var * expr * alloc_target)
  | Free of expr
  | Fork of (var option * expr * expr list)
  | Acquire of expr
  | Release of expr
  | AtomicBegin
  | AtomicEnd
  | Exit
  | PrintBounds of var

(** Definition kind *)
and defkind =
  | Assign of (var * expr)
  | Store of (ap * expr)
  | Call of (var option * expr * expr list)
  | Assume of bexpr
  | Initial
  | Assert of bexpr * string
  | AssertMemSafe of expr * string
  | Return of expr option
  | Builtin of builtin

and def =
  { did : int;
    dloc : Cil.location;
    mutable dkind : defkind }

(** Open types for folding *)
type ('a, 'b, 'c) open_expr =
  | OHavoc         of typ
  | OConstant      of constant
  | OCast          of typ * 'a
  | OBinaryOp      of 'a * binop * 'a * typ
  | OUnaryOp       of unop * 'a * typ
  | OAccessPath    of 'c
  | OBoolExpr      of 'b
  | OAddrOf        of 'c
type ('a, 'b) open_bexpr =
  | OAtom of (pred * 'a * 'a)
  | OAnd of ('b * 'b)
  | OOr of ('b * 'b)

type ('a, 'b, 'c) expr_algebra = ('a, 'b, 'c) open_expr -> 'a
type ('a, 'b) bexpr_algebra = ('a, 'b) open_bexpr -> 'b


let cil_typ_width t =
  match Cil.constFold true (Cil.SizeOf t) with
  | Cil.Const Cil.CInt64 (i, _, _) -> Int64.to_int i
  | _ -> assert false

(* If the width of a float/integer type cannot be determined, use
   unknown_width *)
let _ = Cil.initCIL ()
let unknown_width = 0
let char_width = 1
let bool_width = 1
let machine_int_width = cil_typ_width (Cil.TInt (Cil.IInt, []))
let pointer_width = cil_typ_width (Cil.TPtr (Cil.TInt (Cil.IInt, []), []))
let typ_string = Concrete (Pointer (Concrete (Int char_width)))

(* ========================================================================== *)

(* Functions on types *)
let resolve_type = function
  | Named (_, ctyp) -> !ctyp
  | Concrete ctyp   -> ctyp

let rec typ_width typ = match resolve_type typ with
  | Int k -> k
  | Float k -> k
  | Void -> 0
  | Record record ->
    List.fold_left (+) 0 (List.map field_width record.rfields)
  | Union record ->
    List.fold_left (max) 0 (List.map field_width record.rfields)
  | Lock -> 2 * machine_int_width
  | Func (_, _) -> pointer_width
  | Pointer _ -> pointer_width
  | Array (typ, None) -> unknown_width
  | Array (typ, Some k) -> typ_width typ * k
  | Dynamic -> unknown_width
  | Enum _ -> machine_int_width
and field_width fi = typ_width fi.fityp

let text = Format.pp_print_string

let rec format_ctyp formatter = function
  | Void -> text formatter "void"
  | Lock -> text formatter "lock"
  | Int 0 -> text formatter "int<??>"
  | Int 1 -> text formatter "char"
  | Int 4 -> text formatter "int32"
  | Int 8 -> text formatter "int64"
  | Int k -> Format.fprintf formatter "int<%d>" k
  | Float 0 -> text formatter "float<??>"
  | Float k -> Format.fprintf formatter "float<%d>" k
  | Pointer t -> Format.fprintf formatter "@[<hov 0>*%a@]" format_typ t
  | Array (t, Some i) -> Format.fprintf formatter "%a[%d]" format_typ t i
  | Array (t, None) -> Format.fprintf formatter "%a[]" format_typ t
  | Record r -> text formatter ("Record " ^ r.rname)
  | Enum e -> text formatter ("Enum " ^ e.enname)
  | Func (ret, args) ->
    Format.fprintf formatter "fun (%a) -> %a"
      (Putil.format_list format_typ) args
      format_typ ret
  | Union r -> text formatter ("Union " ^ r.rname)
  | Dynamic -> text formatter "dynamic"
and format_typ formatter = function
  | Named (name, i) -> text formatter ("`" ^ name ^ "`")
  | Concrete ctyp   -> format_ctyp formatter ctyp

(** Try to resolve an offset to a sequence of field accesses. *)
let rec resolve_offset typ offset =
  match resolve_type typ, offset with
  | (Record ri, OffsetFixed offset) ->
    let found x =
      let new_offset = OffsetFixed (offset - x.fioffset) in
      match resolve_offset x.fityp new_offset with
      | Some fs -> Some (x::fs)
      | None    -> None
    in
    let rec go = function
      | (x::_) when x.fioffset = offset -> found x
      | [x] -> found x
      | (x::y::zs) when offset < y.fioffset -> found x
      | (x::y::zs) -> go (y::zs)
      | [] -> None
    in
    go ri.rfields
  | (Union _, _) -> None (* not unique!*)
  | (x, OffsetFixed 0) -> Some []
  | _ -> None

let opt_equiv f x y = match (x,y) with
  | (Some x, Some y) -> f x y
  | (None, None) -> true
  | _ -> false

let list_equiv p xs ys =
  (List.length xs) = (List.length ys)
  && List.for_all2 p xs ys

(** Types are equivalent if they agree on everything but record keys *)
let rec ctyp_equiv s t = match (s,t) with
  | (Void, Void) -> true
  | (Lock, Lock) -> true
  | (Int sk, Int tk) -> sk = tk
  | (Float sk, Float tk) -> sk = tk
  | (Pointer s, Pointer t) -> typ_equiv s t
  | (Array (s, s_size), Array (t, t_size)) ->
    typ_equiv s t && opt_equiv (=) s_size t_size
  | (Record s_ri, Record t_ri) -> record_equiv s_ri t_ri
  | (Enum s_ei, Enum t_ei) -> enum_equiv s_ei t_ei
  | (Func (s_ret, s_args), Func (t_ret, t_args)) ->
    typ_equiv s_ret t_ret && (list_equiv typ_equiv s_args t_args)
  | (Union s_ri, Union t_ri) -> record_equiv s_ri t_ri
  | (Dynamic, Dynamic) -> true
  | _ -> false
and typ_equiv s t = match s,t with
  | (Named (s, _), Named (t, _)) -> s = t
  | _ -> ctyp_equiv (resolve_type s) (resolve_type t)
and record_equiv s t =
  s.rname = t.rname && list_equiv field_equiv s.rfields t.rfields
and field_equiv f g =
  f.finame = g.finame && typ_equiv f.fityp g.fityp
and enum_equiv s t =
  s.enname = t.enname && list_equiv (=) s.enitems t.enitems

let is_pointer_type x = match resolve_type x with
  | Array _ -> true
  | Pointer _ -> true
  | Func _ -> true
  | _ -> false

let is_numeric_type x = match resolve_type x with
  | Int _ | Float _ | Enum _ -> true
  | _ -> false

let rec typ_get_offsets typ = match resolve_type typ with
  | Record ri ->
    let f rest fi =
      Offset.Set.union (Offset.Set.map
                          (Offset.add (OffsetFixed fi.fioffset))
                          (typ_get_offsets fi.fityp))
        rest
    in
    List.fold_left f Offset.Set.empty ri.rfields	
  | Union ri ->
    let f rest fi = Offset.Set.union (typ_get_offsets fi.fityp) rest in
    List.fold_left f Offset.Set.empty ri.rfields
  | _ -> Offset.Set.singleton (OffsetFixed 0)

module Var = struct
  include Putil.MakeCoreType(struct
      type t = var deriving (Compare)
      let compare = Compare_t.compare
      let hash (x, y) = Hashtbl.hash (Varinfo.hash x, y)
      let equal = Eq.eq<var>
      include Putil.MakeFmt(struct
          type a = t
          let format formatter (var, offset) =
            match resolve_offset var.vtyp offset with
            | Some [] -> Varinfo.format formatter var
            | Some xs ->
              let pp formatter f = Format.pp_print_string formatter f.finame in
              Format.fprintf formatter "%a.%a"
                Varinfo.format var
                (ApakEnum.pp_print_enum
                   ~pp_sep:(fun formatter () ->
                       Format.pp_print_string formatter ".")
                   pp)
                (BatList.enum xs)

            | None ->
              Format.fprintf formatter "%a.%a"
                Varinfo.format var
                Offset.format offset
        end)
    end)
  let get_type (v, offset) =
    match resolve_offset v.vtyp offset with
    | Some [] -> v.vtyp
    | Some xs -> (BatList.last xs).fityp
    | None -> Concrete Dynamic
  let get_visibility (v, _) = Varinfo.get_visibility v
  let is_global = vz_is_global % get_visibility
  let is_shared = vz_is_shared % get_visibility
  let subscript (v,offset) ss = ({ v with vsubscript = ss }, offset)
  let unsubscript var = subscript var 0
  let get_subscript v = (fst v).vsubscript
  let mk varinfo = (varinfo, OffsetFixed 0)
  let get_id (v,_) = v.vid
end

(* Functions on expressions ***************************************************)
let rec fold_expr_only f = function
  | Havoc typ -> f (OHavoc typ)
  | Constant c -> f (OConstant c)
  | Cast (typ, expr) -> f (OCast (typ, fold_expr_only f expr))
  | BinaryOp (a, op, b, typ) ->
    f (OBinaryOp (fold_expr_only f a, op, fold_expr_only f b, typ))
  | UnaryOp (op, a, typ) ->
    f (OUnaryOp (op, fold_expr_only f a, typ))
  | AccessPath ap -> f (OAccessPath ap)
  | BoolExpr bexpr -> f (OBoolExpr bexpr)
  | AddrOf ap -> f (OAddrOf ap)

let rec fold_bexpr_only f = function
  | And (x, y) -> f (OAnd (fold_bexpr_only f x, fold_bexpr_only f y))
  | Or (x, y) -> f (OOr (fold_bexpr_only f x, fold_bexpr_only f y))
  | Atom (p, x, y) -> f (OAtom (p, x, y))

let rec fold_expr f g =
  let h = function
    | OBoolExpr bexpr -> f (OBoolExpr (fold_bexpr f g bexpr))
    | OHavoc typ -> f (OHavoc typ)
    | OConstant c -> f (OConstant c)
    | OCast (typ, expr) -> f (OCast (typ, expr))
    | OBinaryOp (a, op, b, typ) -> f (OBinaryOp (a, op, b, typ))
    | OUnaryOp (op, a, typ) -> f (OUnaryOp (op, a, typ))
    | OAccessPath ap -> f (OAccessPath ap)
    | OAddrOf ap -> f (OAddrOf ap)
  in
  fold_expr_only h
and fold_bexpr f g =
  let h = function
    | OAtom (pred, left, right) ->
      g (OAtom (pred, fold_expr f g left, fold_expr f g right))
    | OAnd (x, y) -> g (OAnd (x, y))
    | OOr (x, y) -> g (OOr (x, y))
  in
  fold_bexpr_only h

let expr_of_offset = function
  | OffsetUnknown -> Havoc (Concrete (Int unknown_width))
  | OffsetFixed n -> Constant (CInt (n, unknown_width))

let rec expr_type = function
  | Havoc typ -> typ
  | Constant (CInt (_, ik)) -> Concrete (Int ik)
  | Constant (CString _) ->
    (* probably Array (Int IChar), but this should be checked ... *)
    assert false
  | Constant (CChar _) -> Concrete (Int 1)
  | Constant (CFloat (_, fk)) -> Concrete (Float fk)
  | Cast (typ, _) -> typ
  | BinaryOp (_, _, _, typ) -> typ
  | UnaryOp (_, _, typ) -> typ
  | AccessPath ap -> ap_type ap
  | BoolExpr _ -> Concrete (Int 1)
  | AddrOf ap -> Concrete (Pointer (ap_type ap))
and ap_type ap =
  let deref_type x = match resolve_type x with
    | Array (typ, _) -> typ
    | Pointer typ -> typ
    | Func _ -> x (* todo *)
    | Dynamic -> Concrete Dynamic
    | typ -> Concrete (Pointer (Concrete Dynamic))
    (*
      Log.debugf "Deref type: %a" format_ctyp typ;
      assert false
    *)
  in
  match ap with
  | Variable v -> Var.get_type v
  | Deref (BinaryOp (ptr,
                     Add,
                     Constant (CInt (off, _)),
                     Concrete (Pointer typ))) -> begin
      match resolve_offset typ (OffsetFixed off) with
      | None -> Concrete Dynamic
      | Some [] -> typ
      | Some xs -> (BatList.last xs).fityp
    end
  | Deref (AccessPath ap) -> deref_type (ap_type ap)
  | Deref _ -> Concrete Dynamic

(* Try to rewrite an expression as ptr + constant offset.  This could be made
   significantly more general. *)
let to_pointer_offset = function
  | BinaryOp (ptr, Add, Constant (CInt (off, _)), typ)
  | BinaryOp (Constant (CInt (off, _)), Add, ptr, typ) -> begin
      match resolve_type (expr_type ptr) with
      | Pointer _ -> Some (ptr, off)
      | _ -> None
    end
  | _ -> None

let rec format_expr formatter = function
  | Havoc _ -> Format.pp_print_string formatter "*"
  | Cast (typ, ex) ->
    Format.fprintf formatter "(%a)%a"
      format_typ typ
      format_expr ex
  | BinaryOp (ex1, b, ex2, tp) ->
    let op = match b with
      | Add    -> "+"
      | Minus  -> "-"
      | Mult   -> "*"
      | Div    -> "/"
      | Mod    -> "%"
      | ShiftL -> "<<"
      | ShiftR -> ">>"
      | BXor   -> "^"
      | BAnd   -> "&"
      | BOr    -> "|"
    in
    Format.fprintf formatter "@[<hov 0>(%a%s%a)@]"
      format_expr ex1
      op
      format_expr ex2
  | UnaryOp (u, ex, tp) ->
    let op = match u with
      | Neg  -> "-"
      | BNot -> "~"
    in
    Format.fprintf formatter "%s%a" op format_expr ex
  | Constant (CInt (i, _)) -> Format.pp_print_int formatter i
  | Constant (CString s) -> Format.fprintf formatter "\"%s\"" s
  | Constant (CChar c) -> Format.pp_print_char formatter c
  | Constant (CFloat (flt,_)) -> Format.pp_print_float formatter flt
  | AccessPath ap -> format_ap formatter ap
  | BoolExpr b -> format_bexpr formatter b
  | AddrOf ap -> Format.fprintf formatter "&%a" format_ap ap
and format_bexpr formatter  = function
  | And (left, right) ->
    Format.fprintf formatter "%a&&%a"
      format_bexpr left
      format_bexpr right
  | Or (left, right) ->
    Format.fprintf formatter "%a||%a"
      format_bexpr left
      format_bexpr right
  | Atom (pred, left, right) ->
    let pred = match pred with
      | Lt -> "<"
      | Le -> "<="
      | Eq -> "=="
      | Ne -> "!="
    in
    Format.fprintf formatter "%a%s%a"
      format_expr left
      pred
      format_expr right
and format_ap formatter = function
  | Variable v -> Var.format formatter v
  | Deref expr -> match to_pointer_offset expr with
    | Some (ptr, offset) -> begin match resolve_type (expr_type expr) with
        | Pointer typ -> begin
            match resolve_offset typ (OffsetFixed offset) with
            | Some [] | None ->
              Format.fprintf formatter "(*%a)" format_expr expr
            | Some xs ->
              Format.fprintf formatter "(%a)->%s"
                format_expr ptr
                (String.concat "." (List.map (fun f -> f.finame) xs))
          end
        | _ -> Format.fprintf formatter "(*%a)" format_expr expr
      end
    | None -> Format.fprintf formatter "(*%a)" format_expr expr

let show_expr expr = Putil.pp_string format_expr expr
let show_bexpr bexpr = Putil.pp_string format_bexpr bexpr

let expr_compare = Compare.compare<expr>
let bexpr_compare = Compare.compare<bexpr>
let ap_compare = Compare.compare<ap>

let hash_expr_alg hash_ap = function
  | OAccessPath a -> hash_ap a lsl 2
  | OAddrOf a -> hash_ap a lsl 2 + 1
  | x -> Hashtbl.hash x lsl 2 + 2
let hash_bexpr_alg = Hashtbl.hash

let rec ap_hash = function
  | Variable v -> Var.hash v lsl 1
  | Deref expr -> (expr_hash expr) lsl 1 + 1
and expr_hash expr =
  fold_expr (hash_expr_alg ap_hash) hash_bexpr_alg expr
and bexpr_hash bexpr =
  fold_bexpr (hash_expr_alg ap_hash) hash_bexpr_alg bexpr

let rec strip_all_casts_ap = function
  | Variable v -> Variable v
  | Deref expr -> Deref (strip_all_casts_expr expr)
and strip_all_casts_expr expr =
  let f = function
    | OHavoc typ -> Havoc typ
    | OConstant const -> Constant const
    | OCast (_, expr) -> expr
    | OBinaryOp (a, op, b, typ) -> BinaryOp (a, op, b, typ)
    | OUnaryOp (op, a, typ) -> UnaryOp (op, a, typ)
    | OAccessPath ap -> AccessPath (strip_all_casts_ap ap)
    | OBoolExpr b -> BoolExpr (strip_all_casts_bexpr b)
    | OAddrOf ap -> AccessPath (strip_all_casts_ap ap)
  in
  fold_expr_only f expr
and strip_all_casts_bexpr bexpr =
  let f = function
    | OAnd (a, b) -> And (a, b)
    | OOr (a, b) -> Or (a, b)
    | OAtom (pred, a, b) ->
      Atom (pred, strip_all_casts_expr a, strip_all_casts_expr b)
  in
  fold_bexpr_only f bexpr


(* Functions on variables *****************************************************)

let get_offsets v =
  let f offset set = Var.Set.add (v, offset) set in
  Offset.Set.fold f (typ_get_offsets v.vtyp) Var.Set.empty

(* Functions on definitions ***************************************************)
let format_builtin formatter = function
  | Alloc (lhs, size, AllocHeap) ->
    Format.fprintf formatter "%a = malloc(%a)"
      Var.format lhs
      format_expr size
  | Alloc (lhs, size, AllocStack) ->
    Format.fprintf formatter "%a = alloca(%a)"
      Var.format lhs
      format_expr size
  | Free (expr) -> Format.fprintf formatter "free(%a)" format_expr expr
  | Fork (lhs, func, args) ->
    begin match lhs with
      | Some v -> Format.fprintf formatter "%a = " Var.format v
      | None    -> ()
    end;
    Format.fprintf formatter "fork(%a, %a)"
      format_expr func
      (ApakEnum.pp_print_enum format_expr) (BatList.enum args)
  | Acquire lock -> Format.fprintf formatter "acquire(%a)" format_expr lock
  | Release lock -> Format.fprintf formatter "release(%a)" format_expr lock
  | AtomicBegin -> Format.pp_print_string formatter "atomic_begin"
  | AtomicEnd -> Format.pp_print_string formatter "atomic_end"
  | Exit -> Format.pp_print_string formatter "exit"
  | PrintBounds v ->
    Format.fprintf formatter "print_bounds(%a)" Var.format v

(** Pretty printing for definitions (needs to be rewritten) *)
let format_dk formatter = function
  | Assign (var, expr) ->
    Format.fprintf formatter "%a=%a"
      Var.format var
      format_expr expr
  | Store (ap, expr) ->
    Format.fprintf formatter "%a=%a"
      format_ap ap
      format_expr expr
  | Call (None, func, args) ->
    Format.fprintf formatter "%a(%a)"
      format_expr func
      (ApakEnum.pp_print_enum format_expr) (BatList.enum args)
  | Call (Some lhs, func, args) ->
    Format.fprintf formatter "%a=%a(%a)"
      Var.format lhs
      format_expr func
      (ApakEnum.pp_print_enum format_expr) (BatList.enum args)
  | Assume expr -> Format.fprintf formatter "assume(%a)" format_bexpr expr
  | Initial -> Format.pp_print_string formatter "initial"
  | Assert (e,msg) ->
    Format.fprintf formatter "assert(%a) : %s" format_bexpr e msg
  | AssertMemSafe (e,msg) ->
    Format.fprintf formatter "memsafe(%a) : %s" format_expr e msg
  | Return None -> Format.pp_print_string formatter "return"
  | Return (Some e) -> Format.fprintf formatter "return %a" format_expr e
  | Builtin b -> format_builtin formatter b

let format_def formatter def =
  Format.fprintf formatter "%d : %a"
    def.did
    format_dk def.dkind

let unknown_loc = Cil.locUnknown

let eval_binop op i j = match op with
  | Add    -> i + j
  | Minus  -> i - j
  | Mult   -> i * j
  | Div    -> i / j
  | Mod    -> i mod j
  | ShiftL -> i lsl j
  | ShiftR -> i lsr j
  | BXor   -> i lxor j
  | BAnd   -> i land j
  | BOr    -> i lor j

(** Deriving instances *)
module Compare_def = struct
  type a = def
  let compare x y = compare x.did y.did
end
module Show_bexpr = Deriving_Show.Defaults(struct
    type a = bexpr
    let format = format_bexpr
  end)
module Show_expr = Deriving_Show.Defaults(struct
    type a = expr
    let format = format_expr
  end)
module Show_var = Deriving_Show.Defaults(struct
    type a = var
    let format = Var.format
  end)
module Show_ap = Deriving_Show.Defaults(struct
    type a = ap
    let format = format_ap
  end)

(******************************************************************************)
let expr_apply apply_ap f = function
  | OHavoc typ -> f (Havoc typ)
  | OConstant c -> f (Constant c)
  | OCast (typ, expr) -> f (Cast (typ, expr))
  | OBinaryOp (a, op, b, typ) -> f (BinaryOp (a, op, b, typ))
  | OUnaryOp (op, a, typ) -> f (UnaryOp (op, a, typ))
  | OBoolExpr b -> f (BoolExpr b)
  | OAccessPath ap -> f (AccessPath (apply_ap ap))
  | OAddrOf ap -> f (AddrOf (apply_ap ap))
let bexpr_apply f = function
  | OAtom (pred, a, b) -> f (Atom (pred, a, b))
  | OAnd (a, b) -> f (And (a, b))
  | OOr (a, b) -> f (Or (a, b))

let expr_identity f_ap = function
  | OHavoc typ -> Havoc typ
  | OConstant c -> Constant c
  | OCast (typ, expr) -> Cast (typ, expr)
  | OBinaryOp (a, op, b, typ) -> BinaryOp (a, op, b, typ)
  | OUnaryOp (op, a, typ) -> UnaryOp (op, a, typ)
  | OBoolExpr b -> BoolExpr b
  | OAccessPath ap -> AccessPath (f_ap ap)
  | OAddrOf ap -> AddrOf (f_ap ap)
let bexpr_identity = function
  | OAtom (pred, a, b) -> Atom (pred, a, b)
  | OAnd (a, b) -> And (a, b)
  | OOr (a, b) -> Or (a, b)

let expr_partial_identity f_ap = function
  | OHavoc typ -> Some (Havoc typ)
  | OConstant c -> Some (Constant c)
  | OCast (typ, Some expr) -> Some (Cast (typ, expr))
  | OCast (_, _) -> None
  | OBinaryOp (Some left, op, Some right, typ) ->
    Some (BinaryOp (left, op, right, typ))
  | OBinaryOp (_, _, _, _) -> None
  | OUnaryOp (op, Some a, typ) -> Some (UnaryOp (op, a, typ))
  | OUnaryOp (_, _, _) -> None
  | OBoolExpr (Some bexpr) -> Some (BoolExpr bexpr)
  | OBoolExpr None -> None
  | OAccessPath ap -> begin match f_ap ap with
      | Some ap -> Some (AccessPath ap)
      | None    -> None
    end
  | OAddrOf ap -> begin match f_ap ap with
      | Some ap -> Some (AddrOf ap)
      | None    -> None
    end
let bexpr_partial_identity = function
  | OAtom (pred, Some left, Some right) -> Some (Atom (pred, left, right))
  | OAtom (_, _, _) -> None
  | OAnd (Some left, Some right) -> Some (And (left, right))
  | OAnd (_, _) -> None
  | OOr (Some left, Some right) -> Some (Or (left, right))
  | OOr (_, _) -> None

(* A variable is free in an expression if it occurs in that expression. *)
let free_vars_expr_alg free_vars_ap = function
  | OHavoc _ | OConstant _ -> Var.Set.empty
  | OAddrOf ap | OAccessPath ap -> free_vars_ap ap
  | OUnaryOp (_, uses, _) | OCast (_, uses) | OBoolExpr uses -> uses
  | OBinaryOp (use1, _, use2, _) -> Var.Set.union use1 use2
let free_vars_bexpr_alg = function
  | OAtom (_, left, right) | OAnd (left, right) | OOr (left, right) ->
    Var.Set.union left right

let rec free_vars_expr expr =
  fold_expr (free_vars_expr_alg free_vars_ap) free_vars_bexpr_alg expr
and free_vars_bexpr bexpr =
  fold_bexpr (free_vars_expr_alg free_vars_ap) free_vars_bexpr_alg bexpr
and free_vars_ap = function
  | Variable v -> Var.Set.singleton v
  | Deref expr -> free_vars_expr expr

module CoreAP =
  Putil.MakeCoreType(struct
    type t = ap
    module Compare_t = struct
      type a = ap
      let compare = ap_compare
    end
    include Putil.MakeFmt(struct
        type a = t
        let format = format_ap
      end)
    let compare = ap_compare
    let equal a b = ap_compare a b = 0
    let hash = ap_hash
  end)

(* An access path is used by an expression if it is read, but is not a
   subexpression of another access path.  If a value is provided for every
   used access path, then that expression can be evaluated. *)
let uses_expr_alg expr_uses = function
  | OAccessPath x -> CoreAP.Set.singleton x
  | OAddrOf (Deref x) -> expr_uses x
  | OHavoc _ | OConstant _ | OAddrOf _ -> CoreAP.Set.empty
  | OUnaryOp (_, uses, _) | OCast (_, uses) | OBoolExpr uses -> uses
  | OBinaryOp (use1, _, use2, _) -> CoreAP.Set.union use1 use2
let uses_bexpr_alg = function
  | OAtom (_, left, right) | OAnd (left, right) | OOr (left, right) ->
    CoreAP.Set.union left right

let rec get_uses_expr expr =
  fold_expr (uses_expr_alg get_uses_expr) uses_bexpr_alg expr
let get_uses_bexpr = fold_bexpr (uses_expr_alg get_uses_expr) uses_bexpr_alg

(* An access path is accessed by an expression if it is read in the concrete
   execution of that expression.  *)
let rec accessed_expr = function
  | Havoc _ | Constant _ -> CoreAP.Set.empty
  | Cast (_, expr) -> accessed_expr expr
  | BinaryOp (left, _, right, _) ->
    CoreAP.Set.union (accessed_expr left) (accessed_expr right)
  | UnaryOp (_, expr, _) -> accessed_expr expr
  | AccessPath ap -> CoreAP.Set.add ap (accessed_ap ap)
  | BoolExpr bexpr -> accessed_bexpr bexpr
  | AddrOf (Deref expr) -> accessed_expr expr
  | AddrOf (Variable _) -> CoreAP.Set.empty
and accessed_bexpr = function
  | Atom (_, left, right) ->
    CoreAP.Set.union (accessed_expr left) (accessed_expr right)
  | And (left, right) | Or (left, right) ->
    CoreAP.Set.union (accessed_bexpr left) (accessed_bexpr right)
and accessed_ap ap =
  CoreAP.Set.add ap (match ap with
      | Deref expr -> accessed_expr expr
      | Variable _ -> CoreAP.Set.empty)


(** Substitute an access path within an expression *)
let rec subst_ap_expr f =
  fold_expr (expr_identity (subst_ap_ap f)) bexpr_identity

(** Substitute an access path within a Boolean expression *)
and subst_ap_bexpr f =
  fold_bexpr (expr_identity (subst_ap_ap f)) bexpr_identity

(** Substitute an access path within an access path *)
and subst_ap_ap f = function
  | Variable _ as var -> f var
  | Deref expr -> f (Deref (subst_ap_expr f expr))

(** Substitute an expression within an expression *)
let rec subst_expr_expr f =
  fold_expr (expr_apply (subst_expr_ap f) f) bexpr_identity

(** Substitute an expression within a Boolean expression *)
and subst_expr_bexpr f =
  fold_bexpr (expr_apply (subst_expr_ap f) f) bexpr_identity

(** Substitute an expression within an access path *)
and subst_expr_ap f = function
  | Deref expr -> Deref (subst_expr_expr f expr)
  | Variable _ as var -> var

let rec subst_var_expr f =
  fold_expr (expr_identity (subst_var_ap f)) bexpr_identity

(** Substitute a variable within a Boolean expression *)
and subst_var_bexpr f =
  fold_bexpr (expr_identity (subst_var_ap f)) bexpr_identity

(** Substitute a variable within an access path *)
and subst_var_ap f = function
  | Variable var -> Variable (f var)
  | Deref expr -> Deref (subst_var_expr f expr)

let rec psubst_var_expr f =
  fold_expr (expr_partial_identity (psubst_var_ap f)) bexpr_partial_identity

(** Partial substitution of a variable within a Boolean expression *)
and psubst_var_bexpr f =
  fold_bexpr (expr_partial_identity (psubst_var_ap f)) bexpr_partial_identity

(** Partial substitution of a variable within an access path *)
and psubst_var_ap f = function
  | Variable var -> begin match f var with
      | Some var -> Some (Variable var)
      | None     -> None
    end
  | Deref expr -> begin match psubst_var_expr f expr with
      | Some expr -> Some (Deref expr)
      | None      -> None
    end

type bexpr_val = BTrue | BFalse | BHavoc | BNone

let expr_zero = Constant (CInt (0, unknown_width))
let expr_one = Constant (CInt (1, unknown_width))
let bexpr_true = Atom (Ne, expr_one, expr_zero)
let bexpr_false = Atom (Eq, expr_one, expr_zero)
let bexpr_havoc = Atom (Ne, (Havoc (Concrete (Int 1))), expr_zero)
let bexpr_equal x y = bexpr_compare x y = 0

let (simplify_expr, simplify_bexpr) =
  let constant_bexpr bexpr =
    if bexpr_equal bexpr bexpr_true then BTrue
    else if bexpr_equal bexpr bexpr_false then BFalse
    else if bexpr_equal bexpr bexpr_havoc then BHavoc
    else BNone
  in
  let f = function
    | OConstant (CInt (i, ik)) -> Constant (CInt (i, ik))
    | OConstant x -> Constant x
    | OCast (typ, e) -> Cast (typ, e)
    | OBinaryOp (Constant (CInt (i, ik)), op, Constant (CInt (j, jk)), typ) ->
      (match op with
       | Add -> Constant (CInt (i + j, ik))
       | Minus -> Constant (CInt (i - j, ik))
       | Mult -> Constant (CInt (i * j, ik))
       | Div -> Constant (CInt (i / j, ik))
       | Mod -> Constant (CInt (i mod j, ik))
       | ShiftL -> Constant (CInt (i lsl j, ik))
       | ShiftR -> Constant (CInt (i lsr j, ik))
       | BXor -> Constant (CInt (i lxor j, ik))
       | BAnd -> Constant (CInt (i land j, ik))
       | BOr -> Constant (CInt (i lor j, ik)))
    | OBinaryOp (left, op, right, typ) -> BinaryOp (left, op, right, typ)
    | OUnaryOp (op, Constant (CInt (i, ik)), typ) ->
      (match op with
       | Neg -> Constant (CInt (0 - i, ik))
       | BNot -> Constant (CInt (lnot i, ik)))
    | OUnaryOp (op, expr, typ) -> UnaryOp (op, expr, typ)
    | OAccessPath ap -> AccessPath ap
    | OBoolExpr expr ->
      (match constant_bexpr expr with
       | BTrue -> Constant (CInt (1, bool_width))
       | BFalse -> Constant (CInt (0, bool_width))
       | BHavoc -> Havoc (Concrete (Int bool_width))
       | BNone -> BoolExpr expr)
    | OHavoc typ -> Havoc typ
    | OAddrOf ap -> AddrOf ap
  in
  let g = function
    | OOr (a, b) ->
      (match (constant_bexpr a, constant_bexpr b) with
       | (BTrue, _) -> bexpr_true
       | (_, BTrue) -> bexpr_true
       | (BFalse, _) -> b
       | (_, BFalse) -> a
       | _ -> if bexpr_equal a b then a else Or (a, b))
    | OAnd (a, b) ->
      (match (constant_bexpr a, constant_bexpr b) with
       | (BFalse, _) -> bexpr_false
       | (_, BFalse) -> bexpr_false
       | (BTrue, _) -> b
       | (_, BTrue) -> a
       | _ -> if bexpr_equal a b then a else And (a, b))
    | OAtom (Eq, Havoc _, _) -> bexpr_havoc
    | OAtom (Eq, _, Havoc _) -> bexpr_havoc
    | OAtom (Ne, Havoc _, _) -> bexpr_havoc
    | OAtom (Ne, _, Havoc _) -> bexpr_havoc
    | OAtom (pred, Constant (CInt (i, _)), Constant (CInt (j, _))) ->
      let tr_bool b = if b then bexpr_true else bexpr_false in
      (match pred with
       | Lt -> tr_bool (i < j)
       | Le -> tr_bool (i <= j)
       | Eq -> tr_bool (i = j)
       | Ne -> tr_bool (i != j))
    | OAtom (pred, a, b) -> Atom (pred, a, b)
  in
  (fold_expr f g, fold_bexpr f g)

(******************************************************************************)
(** Access paths *)
module AP = struct
  include CoreAP
  let get_type = ap_type
  let get_ctype ap = resolve_type (get_type ap)

  let addr_of = function
    | Deref expr -> expr
    | var        -> AddrOf var

  let rec get_visibility = function
    | Deref _ -> VzGlobal
    | Variable v -> Var.get_visibility v
  let is_global = vz_is_global % get_visibility
  let is_shared = vz_is_shared % get_visibility

  let subscript n ap = subst_var_ap (fun v -> Var.subscript v n) ap
  let unsubscript ap = subst_var_ap Var.unsubscript ap

  let subst_var = subst_var_ap
  let psubst_var = psubst_var_ap
  let subst_ap = subst_ap_ap
  let subst_expr = subst_expr_ap
  let free_vars = free_vars_ap
  let accessed = accessed_ap

  let strip_all_casts = strip_all_casts_ap

  (** Access an offset of an access path *)
  let offset ap offset = match ap with
    | Deref expr ->
      Deref (BinaryOp (expr, Add, expr_of_offset offset, expr_type expr))
    | Variable (v, vof) -> Variable (v, Offset.add vof offset)
end

(******************************************************************************)
(** Expressions *)
module Expr = struct
  include Putil.MakeCoreType(struct
      type t = expr
      module Compare_t = struct
        type a = expr
        let compare = expr_compare
      end
      include Putil.MakeFmt(struct
          type a = t
          let format = format_expr
        end)
      let compare = expr_compare
      let equal a b = expr_compare a b = 0
      let hash = expr_hash
    end)

  (* todo: conversion rules *)
  let add x y = BinaryOp (x, Add, y, Concrete Dynamic)
  let sub x y = BinaryOp (x, Minus, y, Concrete Dynamic)
  let mul x y = BinaryOp (x, Mult, y, Concrete Dynamic)
  let div x y = BinaryOp (x, Div, y, Concrete Dynamic)
  let modulo x y = BinaryOp (x, Mod, y, Concrete Dynamic)
  let neg x = UnaryOp (Neg, x, Concrete Dynamic)
  let addr_of ap =
    match ap with
    | Deref expr -> expr
    | Variable v -> begin
        (fst v).vaddr_taken <- true;
        AddrOf ap
      end

  let const_int x = Constant (CInt (x, unknown_width))
  let zero = const_int 0
  let one = const_int 1
  let null typ = Cast (typ, zero)

  let subst_var = subst_var_expr
  let psubst_var = psubst_var_expr
  let subst_ap = subst_ap_expr
  let subst_expr = subst_expr_expr

  let free_vars = free_vars_expr
  let accessed = accessed_expr
  let get_uses = get_uses_expr

  let simplify = simplify_expr
  let rec strip_casts exp = match exp with
    | Cast (_, exp) -> strip_casts exp
    | _ -> exp
  let strip_all_casts = strip_all_casts_expr
  let get_type = expr_type
  let fold = fold_expr_only
  let deep_fold = fold_expr
end

(******************************************************************************)
(** Boolean expressions *)
module Bexpr = struct
  include Putil.MakeCoreType(struct
      type t = bexpr
      module Compare_t = struct
        type a = bexpr
        let compare = bexpr_compare
      end
      include Putil.MakeFmt(struct
          type a = t
          let format = format_bexpr
        end)
      let compare = bexpr_compare
      let equal a b = bexpr_compare a b = 0
      let hash = bexpr_hash
    end)

  let rec negate = function
    | And (left, right) -> Or (negate left, negate right)
    | Or (left, right) -> And (negate left, negate right)
    | Atom (Lt, left, right) -> Atom (Le, right, left)
    | Atom (Le, left, right) -> Atom (Lt, right, left)
    | Atom (Eq, left, right) -> Atom (Ne, left, right)
    | Atom (Ne, left, right) -> Atom (Eq, left, right)

  let implies x y = Or (y, negate x)
  let gt left right = Atom (Lt, right, left)
  let ge left right = Atom (Le, right, left)

  let of_expr = function
    | BoolExpr b -> b
    | expr        -> Atom (Ne, expr, Expr.zero)
  let ktrue = Atom (Le, Expr.zero, Expr.zero)
  let kfalse = negate ktrue
  let havoc = of_expr (Havoc (Concrete (Int 1)))

  let subst_var = subst_var_bexpr
  let psubst_var = psubst_var_bexpr
  let subst_ap = subst_ap_bexpr
  let subst_expr = subst_expr_bexpr

  let free_vars = free_vars_bexpr
  let accessed = accessed_bexpr
  let get_uses = get_uses_bexpr

  let eval bexpr =
    let bexpr = simplify_bexpr bexpr in
    if bexpr_equal bexpr bexpr_true then Some true
    else if bexpr_equal bexpr bexpr_false then Some false
    else None

  let dnf bexpr =
    let f = function
      | OAnd (x, y) ->
        ApakEnum.cartesian_product (BatList.enum x) (BatList.enum y)
        |> BatEnum.fold (fun r (x, y) -> (x @ y)::r) []
      | OOr (x, y) -> x@y
      | OAtom (p, a, b) -> [[Atom (p,a,b)]]
    in
    let dnf_list = fold_bexpr_only f bexpr in
    let construct_minterm = BatList.reduce (fun x y -> And (x, y)) in
    let minterms = List.map construct_minterm dnf_list in
    BatList.reduce (fun x y -> Or (x, y)) minterms

  let simplify = simplify_bexpr
  let strip_all_casts = strip_all_casts_bexpr
  let fold = fold_bexpr_only
  let deep_fold = fold_bexpr
end

(******************************************************************************)
(** Definitions *)
let dk_get_defs defkind = match defkind with
  | Assign (lhs, _) -> AP.Set.singleton (Variable lhs)
  | Store (lhs, _) -> AP.Set.singleton lhs
  | Call (Some lhs, _, _) -> AP.Set.singleton (Variable lhs)
  | Call (None, _, _) -> AP.Set.empty
  | Assume expr -> Bexpr.get_uses expr
  | Assert (expr, _) -> Bexpr.get_uses expr
  | AssertMemSafe (expr, _) -> Expr.get_uses expr
  | Initial -> AP.Set.empty
  | Return _ -> AP.Set.empty
  | Builtin (Alloc (lhs, _, _)) -> AP.Set.singleton (Variable lhs)
  | Builtin (Fork (Some lhs, _, _)) -> AP.Set.singleton (Variable lhs)
  | Builtin (Fork (None, _, _)) -> AP.Set.empty
  | Builtin (Free _) -> AP.Set.empty
  | Builtin (Acquire _) | Builtin (Release _) -> AP.Set.empty
  | Builtin AtomicBegin | Builtin AtomicEnd -> AP.Set.empty
  | Builtin Exit -> AP.Set.empty
  | Builtin PrintBounds _ -> AP.Set.empty

let dk_assigned_var = function
  | Assign (v, _)
  | Store (Variable v, _)
  | Call (Some v, _, _)
  | Builtin (Alloc (v, _, _))
  | Builtin (Fork (Some v, _, _)) -> Some v

  | Store _ | Assume _ | Assert _ | Initial | Return _
  | Call (_, _, _) | AssertMemSafe _ | Builtin (Free _)
  | Builtin (Fork (None, _, _))
  | Builtin (Acquire _) | Builtin (Release _)
  | Builtin AtomicBegin | Builtin AtomicEnd
  | Builtin Exit
  | Builtin (PrintBounds _) ->
    None

let rec lhs_accessed = function
  | Variable v -> AP.Set.empty
  | Deref expr -> Expr.accessed expr

let dk_get_accessed = function
  | Assign (_, rhs) -> Expr.accessed rhs
  | Store (ap, rhs) ->
    AP.Set.union (lhs_accessed ap) (Expr.accessed rhs)
  | Call (_, callee, args) | Builtin (Fork (_, callee, args)) -> 
    let f rest expr = AP.Set.union (Expr.accessed expr) rest in
    List.fold_left f (Expr.accessed callee) args
  | Assume bexpr | Assert (bexpr, _) -> Bexpr.accessed bexpr
  | AssertMemSafe (expr, _) -> Expr.accessed expr
  | Initial -> AP.Set.empty
  | Return (Some expr) -> Expr.accessed expr
  | Return None -> AP.Set.empty
  | Builtin (Alloc (_, expr, _)) -> Expr.accessed expr
  | Builtin (Free expr) -> Expr.accessed expr
  | Builtin (Acquire expr) | Builtin (Release expr) -> Expr.accessed expr
  | Builtin AtomicBegin | Builtin AtomicEnd -> AP.Set.empty
  | Builtin Exit -> AP.Set.empty
  | Builtin (PrintBounds v) -> AP.Set.singleton (Variable v)

let lhs_free_vars = function
  | Variable v -> Var.Set.singleton v
  | ap -> AP.free_vars ap

let dk_free_vars = function
  | Assign (var, rhs) -> Var.Set.add var (Expr.free_vars rhs)
  | Store (ap, rhs) ->
    Var.Set.union (lhs_free_vars ap) (Expr.free_vars rhs)
  | Call (lhs, callee, args) ->
    let f rest exp = Var.Set.union (Expr.free_vars exp) rest in
    let accessed = List.fold_left f (Expr.free_vars callee) args in
    begin match lhs with
      | Some v -> Var.Set.add v accessed
      | None -> accessed
    end
  | Assume bexpr | Assert (bexpr, _) -> Bexpr.free_vars bexpr
  | AssertMemSafe (expr, _) -> Expr.free_vars expr
  | Initial -> Var.Set.empty
  | Return (Some expr) -> Expr.free_vars expr
  | Return None -> Var.Set.empty
  | Builtin (Alloc (lhs, expr, _)) ->
    Var.Set.add lhs (Expr.free_vars expr)
  | Builtin (Fork (Some lhs, _, _)) -> Var.Set.singleton lhs
  | Builtin (Fork (None, _, _)) -> Var.Set.empty
  | Builtin (Free expr) -> Expr.free_vars expr
  | Builtin (Acquire expr) | Builtin (Release expr) -> Expr.free_vars expr
  | Builtin AtomicBegin | Builtin AtomicEnd -> Var.Set.empty
  | Builtin Exit -> Var.Set.empty
  | Builtin (PrintBounds v) -> Var.Set.singleton v

let exprlist_uses =
  let f l e = AP.Set.union (Expr.get_uses e) l in
  List.fold_left f AP.Set.empty

let rec dk_get_uses = function
  | Assign (_, expr) -> Expr.get_uses expr
  | Store (_, expr) -> Expr.get_uses expr
  | Call (_, func, args) -> exprlist_uses (func::args)
  | Assume expr -> Bexpr.get_uses expr
  | Initial -> AP.Set.empty
  | Assert (expr, _) -> Bexpr.get_uses expr
  | AssertMemSafe (expr, _) -> Expr.get_uses expr
  | Return None -> AP.Set.empty
  | Return (Some expr) -> Expr.get_uses expr
  | Builtin (Alloc (_, expr, _)) -> Expr.get_uses expr
  | Builtin (Free expr) -> Expr.get_uses expr
  | Builtin (Fork (_, func, args)) -> exprlist_uses (func::args)
  | Builtin (Acquire expr) -> Expr.get_uses expr
  | Builtin (Release expr) -> Expr.get_uses expr
  | Builtin AtomicBegin | Builtin AtomicEnd -> AP.Set.empty
  | Builtin Exit -> AP.Set.empty
  | Builtin (PrintBounds v) -> AP.Set.singleton (Variable v)

module Def = struct
  include Putil.MakeCoreType(struct
      type t = def
      module Compare_t = struct
        type a = def
        let compare x y = Pervasives.compare x.did y.did
      end
      include Putil.MakeFmt(struct
          type a = t
          let format = format_def
        end)
      let hash x = Hashtbl.hash x.did
      let compare = Compare_t.compare
      let equal x y = x.did = y.did
    end)

  (* To keep track of the max_id of the definition hash table *)
  let def_max_id = ref 0
  let def_increase_id () = def_max_id := !(def_max_id) + 1; !def_max_id;;

  let mk ?(loc=Cil.locUnknown) dk =
    let id = def_increase_id () in
    { did = id; dloc = loc; dkind = dk }

  let get_location def = def.dloc

  let clone def = mk ~loc:(get_location def) def.dkind
  let initial = mk Initial

  let get_defs def = dk_get_defs def.dkind
  let get_uses def = dk_get_uses def.dkind
  let get_accessed def = dk_get_accessed def.dkind

  let free_vars def = dk_free_vars def.dkind
  let assigned_var def = dk_assigned_var def.dkind
  let set_max_id k =
    if k > !def_max_id then
      def_max_id := k
end
