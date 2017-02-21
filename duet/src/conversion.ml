open InterIR
open CfgIr
open Core
open Printf
open String

let tmp_file = ref {filename="tmp";threads=[];funcs=[];entry_points=[];vars=[];types=[];globinit=None}
let glob_map = ref []
let fvars = ref []
let print_list = ref []
let current_loc_map = ref []
let current_arg_map = ref []
let func_insert_map = ref []
let tick_list = ref []
let assume_assert_file = "assume_assert.txt"
let cfg_out_file = "intercfg.txt"
let print_file = "print.txt"


let rec convert_type t =
    match t with
      InterIR.Int(s) -> Concrete(Int(s))
    | InterIR.Void -> Concrete(Void)
    | InterIR.Pointer(p) -> let nt = convert_type p in Concrete(Pointer(nt))
    | InterIR.Array(a) -> let at = convert_type a in Concrete(Array(at,None))
    | InterIR.Unknown -> Concrete(Dynamic)

let convert_global g_var =
  match g_var with
    Var(name, typ) ->
      let v_type = convert_type typ in
      (g_var, mk_global_var !tmp_file name v_type)

let convert_local fname l_var =
  match l_var with
    Var(name, typ) ->
      let v_type = convert_type typ in
      (l_var, mk_local_var fname name v_type)

let get_var v =
    let vexpr = (let is_local = (List.mem_assoc v !current_loc_map) in
      if (is_local) then begin
        List.assoc v !current_loc_map end
      else begin
        let is_arg = List.mem_assoc v !current_arg_map in
          if (is_arg) then begin
            List.assoc v !current_arg_map end
          else begin
            List.assoc v !glob_map end
      end) in
      vexpr


let get_lvar v =
  match v with LVal(va) -> get_var va


let get_value v =
  match v with
    InterIR.Constant(x,s) -> Constant(CInt(x,s))
  | InterIR.Var(name, typ) -> AccessPath(Variable(get_var v))

let convert_binop (binop : InterIR.binop) =
  match binop with
    InterIR.Add -> Add
  | InterIR.Sub -> Minus
  | InterIR.Mult -> Mult
  | InterIR.Div -> Div
  | InterIR.Rem -> Mod
  | InterIR.LShift -> ShiftL
  | InterIR.RShift -> ShiftR
  | InterIR.BXor -> BXor
  | InterIR.BAnd -> BAnd
  | InterIR.BOr  -> BOr

let convert_cop op =
  match op with
    GTE -> (Core.Le, true)
  | GT -> (Core.Lt, true)
  | LTE -> (Core.Le, false)
  | LT -> (Core.Lt, false)
  | NE -> (Core.Ne, false)
  | EQ -> (Core.Eq, false)

let get_type_size typ =
  match typ with
    InterIR.Void -> Core.Constant(CInt(0,4))
    | InterIR.Int(s) -> Core.Constant(CInt(s,4))
    | _ -> Core.Constant(CInt(8,4))

let rec convert_lsum ls =
  match ls with
    LVal(v) -> get_value v
  | UNeg(v) -> ( let sub_val = convert_lsum v in
                 Core.UnaryOp(Core.Neg,sub_val,Core.Concrete(Int(4))))
  | LNeg(v) -> ( let sub_val = convert_lsum v in
                 Core.UnaryOp(Core.BNot,sub_val,Core.Concrete(Int(4))))
  | LExpr(l,op,r) ->  (
    let l_val = convert_lsum l in
    let r_val = convert_lsum r in
    let bop = convert_binop op in
    Core.BinaryOp(l_val,bop,r_val,Core.Concrete(Int(4)))
  )
  | ArrayAccess(Var(name,typ), rh) -> let p = get_value (InterIR.Var(name,typ)) in
                          (match p with
                          AccessPath(x) -> let size = get_type_size typ in
                                           let num_access = convert_lsum rh in
                                           Core.AccessPath(Core.Deref(Core.BinaryOp(p,Core.Add,Core.BinaryOp(num_access,Core.Mult,size,Core.Concrete(Int(4))),Core.Concrete(Int(4)))))
                         | _ -> p)
  | InterIR.Havoc -> Core.Havoc(Core.Concrete (Int(4)))


let convert_insts (inst : inst) =
  match inst with
    Assign(l,r) -> (
      let l_var = get_lvar l in
      let r_val = convert_lsum r in
      [Core.Def.mk (Assign(l_var, r_val))]
    )
  | BinExpr(a,l,bop,r) -> (
      let a_var = get_lvar a in
      let l_val = convert_lsum l in
      let r_val = convert_lsum r in
      let binop = convert_binop bop in
      [Core.Def.mk (Assign (a_var,Core.BinaryOp(l_val,binop,r_val,Core.Concrete(Int(4)))))]
    )
  | Assert(cond, str) -> (
    match cond with
      Jmp -> [Core.Def.mk (Assume (Core.Bexpr.ktrue))]
    | NonDet -> [Core.Def.mk (Assume (Core.Bexpr.ktrue))]
    | Cond(l,cop,r) -> (
      let l_val = convert_lsum l in
      let r_val = convert_lsum r in
      let (op,switch) = convert_cop cop in
      let duet_cond = (
        if switch then begin Core.Atom(op,r_val,l_val) end else begin Core.Atom(op, l_val, r_val) end
      ) in
      [Core.Def.mk (Assert(duet_cond,str))]
      )
    )
  | Assume(cond) -> (
    match cond with
      Jmp -> [Core.Def.mk (Assume (Core.Bexpr.ktrue))]
    | NonDet -> [Core.Def.mk (Assume (Core.Bexpr.ktrue))]
    | Cond(l,cop,r) -> (
      let l_val = convert_lsum l in
      let r_val = convert_lsum r in
      let (op,switch) = convert_cop cop in
      let duet_cond = (
        if switch then begin Core.Atom(op,r_val,l_val) end else begin Core.Atom(op, l_val, r_val) end
      ) in
      [Core.Def.mk (Assume(duet_cond))]
      )
    )
  | Tick(bname,v) -> let lvar = get_lvar bname in
                     let lval = convert_lsum bname in
                     let rval = convert_lsum v in
                     let tick_assume = Core.Def.mk (Assume(Core.Atom(Core.Le,Core.Constant(CInt(0,4)),lval))) in
                     let tick_assume_2 = Core.Def.mk (Assume(Core.Atom(Core.Le,Core.Constant(CInt(0,4)),Core.BinaryOp(lval,Core.Add,rval,Core.Concrete(Int(4)))))) in
                     let tick = Core.Def.mk (Assign (lvar,Core.BinaryOp(lval,Core.Add,rval,Core.Concrete(Int(4))))) in
                     let tick_tail = [tick_assume;tick_assume_2;tick] in
                     tick_list := !tick_list @ tick_tail;
                     []
  | Call(a,name,args) -> (
    let func_var = Core.AddrOf(Variable(List.assoc name !fvars)) in
    let asgn_var = (
      match a with
        Some(v) -> Some(get_lvar v)
      | _ -> None
    ) in
    let create_arg var = (
      convert_lsum var
    ) in
    let arg_list = List.map create_arg args in
    [Core.Def.mk (Call(asgn_var,func_var,arg_list))]
  )

let mk_pt dfunc inst =
  let def = convert_insts inst in
  List.map (CfgBuilder.mk_single dfunc.cfg) def

(*let rec remove_insts hd tl =
  match tl with
    [] -> [hd]
  | _  -> (
    let comp = List.hd tl in
    match comp with
      InterIR.Assert(_,_) -> remove_insts comp (List.tl tl)
    | _ -> hd :: (remove_insts comp (List.tl tl))
  )*)

let convert_parsed_binary opString lhs rhs =
  match opString with
    "*" -> Core.BinaryOp(lhs,Mult,rhs,Core.Concrete(Int(4)))
    | "+" -> Core.BinaryOp(lhs,Add,rhs,Core.Concrete(Int(4)))
    | "-" -> Core.BinaryOp(lhs,Minus,rhs,Core.Concrete(Int(4)))
    | "/" -> Core.BinaryOp(lhs,Div,rhs,Core.Concrete(Int(4)))
    | "==" -> Core.BoolExpr(Core.Atom(Core.Eq,lhs,rhs))
    | "!=" -> Core.BoolExpr(Core.Atom(Core.Ne,lhs,rhs))
    | "<=" -> Core.BoolExpr(Core.Atom(Core.Le,lhs,rhs))
    | ">=" -> Core.BoolExpr(Core.Atom(Core.Le,rhs,lhs))
    | "<" -> Core.BoolExpr(Core.Atom(Core.Lt,lhs,rhs))
    | ">" -> Core.BoolExpr(Core.Atom(Core.Lt,rhs,lhs))
    | "||" -> (match lhs with
              Core.BoolExpr(l) -> (match rhs with
                                  Core.BoolExpr(r) -> Core.BoolExpr(Core.Or(l,r))))
    | "&&" -> (match lhs with
              Core.BoolExpr(l) -> (match rhs with
                                  Core.BoolExpr(r) -> Core.BoolExpr(Core.And(l,r))))

let convert_parsed_unary opString sub_e =
  match opString with
    "-" -> Core.UnaryOp(Core.Neg,sub_e,Core.Concrete(Int(4)))
    | "!" -> Core.UnaryOp(Core.BNot,sub_e,Core.Concrete(Int(4)))

let rec convert_parsed_expr parsed_bexpr =
  match parsed_bexpr with
    Assumeassertparser.Op1(opString, e) -> let sub_e = convert_parsed_expr e in
                          convert_parsed_unary opString sub_e
    | Op2(e1, opString, e2) -> let sub_e1 = convert_parsed_expr e1 in
                               let sub_e2 = convert_parsed_expr e2 in
                               convert_parsed_binary opString sub_e1 sub_e2
    | Int(i) -> Core.Constant(CInt(i,4))
    | Id(x) -> AccessPath(Variable(get_var (InterIR.Var(x,InterIR.Int(4)))))

let convert_bexpr parsed_bexpr is_assume =
  let bexpr = convert_parsed_expr parsed_bexpr in
  let stringbexpr = Assumeassertparser.toString parsed_bexpr in
  match bexpr with
    Core.BoolExpr(bexpr) -> (
  if is_assume then begin
    Core.Def.mk (Core.Assume(bexpr)) end
  else begin
    Core.Def.mk (Core.Assert(bexpr,stringbexpr)) end )

let create_ABExpr (_,blk_type_expr) =
  let blk = int_of_string (List.hd blk_type_expr) in
  let type_expr = List.tl blk_type_expr in
  let assume = (String.compare "Assume" (List.hd type_expr)) == 0 in
  let bexpr = List.hd (List.tl type_expr) in
  Printf.printf "yay\n";
  let tmp = Assumeassertparser.parse_expression bexpr in
  let c_string = Assumeassertparser.toString tmp in
  Printf.printf "parsed: %s\n" c_string;
  let convertedbexpr = convert_bexpr tmp assume in
  (blk,convertedbexpr)

let convert_funcs cs_func =
  let blist = cs_func.fbody in
  let cfg = CfgIr.Cfg.create () in
  let duet_func =
  { CfgIr.fname = fst (List.assoc cs_func.fname !fvars);
    CfgIr.formals = [];
    CfgIr.locals = [];
    CfgIr.cfg = CfgIr.Cfg.create ();
    CfgIr.file = Some(!tmp_file) } in
  let cur_f_inserts = List.filter (function (a,b) -> (String.compare a cs_func.fname) = 0) !func_insert_map in
  current_loc_map := [];
  current_arg_map := [];
  let func_convert_local x = convert_local duet_func x in
  current_arg_map := List.map func_convert_local cs_func.fargs;
  current_loc_map := List.map func_convert_local cs_func.flocs;
  let converted_inserts = List.map create_ABExpr cur_f_inserts in
  let (_,arg_list) = List.split !current_arg_map in
  let arg_vars = List.map fst arg_list in
  let duet_func = {duet_func with CfgIr.formals = arg_vars} in
  let init_vertex = Core.Def.mk (Assume (Core.Bexpr.ktrue)) in
  let block_map = ref [] in
  let mk_func_pt = mk_pt duet_func in
  let convert_blks x blk = (
    let num_insts = List.length blk.binsts in
    let cfg_insts = (
      if num_insts > 0 then begin
      List.map mk_func_pt blk.binsts end
      else [[CfgBuilder.mk_skip duet_func.cfg]]
    ) in
    let mk_t_pt = CfgBuilder.mk_single duet_func.cfg in
    let tick_pt_list = List.map mk_t_pt !tick_list in
    let (_,cur_blk_inserts) = List.split (List.filter (function (a,b) -> (a = x)) converted_inserts) in
    let as_pt_lst = List.map mk_t_pt cur_blk_inserts in
    let updated_list = (List.flatten cfg_insts) @ tick_pt_list @ as_pt_lst in
    tick_list := [];
    let cur_block = CfgBuilder.mk_block duet_func.cfg updated_list in
    block_map := !block_map @ [cur_block];
  ) in
  Array.iteri convert_blks blist;
  CfgBuilder.mk_seq duet_func.cfg (CfgBuilder.mk_single duet_func.cfg init_vertex) (List.hd !block_map);
  let blk_array = Array.of_list !block_map in
    let create_branches x blk = (
      let end_point = blk.btype in
      match end_point with
        Return(ret) -> (
        let ret_point = (match ret with
          None -> CfgBuilder.mk_single duet_func.cfg (Core.Def.mk (Return None))
        | Some(ret_v) -> (let ret_var = get_value ret_v in
          CfgBuilder.mk_single duet_func.cfg (Core.Def.mk (Return (Some(ret_var)))))) in
        let print_hull = List.mem cs_func.fname !print_list in
        let current_blk = Array.get blk_array x in
        if print_hull then begin
          let bvar = get_var (InterIR.Var("bytecodecost",Int(4))) in
          let ph = Core.Def.mk (Builtin (PrintBounds bvar)) in
          let ph_pt = CfgBuilder.mk_single duet_func.cfg ph in
          CfgBuilder.mk_seq duet_func.cfg current_blk ph_pt;
          CfgBuilder.mk_seq duet_func.cfg ph_pt ret_point;
          ()  end
        else begin
          CfgBuilder.mk_seq duet_func.cfg current_blk ret_point;
          ()
        end)
      | Branch(children) ->
        (
          let condition = blk.bcond in
          match condition with
          Some(Cond(l, cop, r)) -> (
            let current_blk = Array.get blk_array x in
            let left = convert_lsum l in
            let right = convert_lsum r in
            let (op,switch) = convert_cop cop in
            let duet_cond = (
            if switch then begin Core.Atom(op,right,left) end else begin Core.Atom(op,left,right) end
            ) in
            let then_child = Array.get blk_array (List.hd children) in
            let else_child = Array.get blk_array  (List.hd (List.tl children))  in
            let bthen = CfgBuilder.mk_seq duet_func.cfg (CfgBuilder.mk_single duet_func.cfg (Core.Def.mk (Assume duet_cond))) then_child in
            let belse = CfgBuilder.mk_seq duet_func.cfg (CfgBuilder.mk_single duet_func.cfg (Core.Def.mk (Assume (Core.Bexpr.negate duet_cond)))) else_child in
            CfgBuilder.mk_seq duet_func.cfg current_blk bthen;
            CfgBuilder.mk_seq duet_func.cfg current_blk belse;
            ()
            )
          | Some(Jmp) ->  (
              let current_blk = Array.get blk_array x in
              let connect_children child = (
                let child_block = Array.get blk_array child in
                CfgBuilder.mk_seq duet_func.cfg current_blk child_block;
                ()
              ) in
              List.iter connect_children children; ()
            )
          | Some(NonDet) -> (
            let current_blk = Array.get blk_array x in
            let connect_children child = (
              let child_block = Array.get blk_array child in
              CfgBuilder.mk_seq duet_func.cfg current_blk child_block;
              ()
            ) in
            List.iter connect_children children; ()
          )
          | None -> let current_blk = Array.get blk_array x in
            let connect_children child = (
              let child_block = Array.get blk_array child in
              CfgBuilder.mk_seq duet_func.cfg current_blk child_block;
              ()
            ) in
            List.iter connect_children children; ()
      )
    ) in
  Array.iteri create_branches blist;
  duet_func

let create_func_var cs_func =
  let ret_var = cs_func.fret in
  let ret_type = (match ret_var with
    Some(Var(name,typ)) -> convert_type typ
  | Some(Constant(_,size)) -> Core.Concrete(Int(size))
  | None -> Core.Concrete(Void)) in
  let num_args = List.length cs_func.fargs in
  let ftype = (if num_args = 0 then begin
    Core.Concrete(Func(ret_type, []))
  end else begin
    let gt_var x = (match x with
                     Var(name,typ) -> convert_type typ
                     | _ -> Core.Concrete(Int(4))
                   ) in
    let type_list = List.map gt_var cs_func.fargs in
    Core.Concrete(Func(ret_type, type_list)) end ) in
  (cs_func.fname, mk_global_var !tmp_file cs_func.fname ftype)

let line_stream_of_channel channel =
  Stream.from
    (fun _ ->
      try Some (input_line channel) with End_of_file -> None);;


let initial_insert_create line =
  let initial_split = Str.split (Str.regexp_string ";") line in
  (List.hd initial_split, List.tl initial_split)

let create_assume_assert_list () =
  let ic = open_in assume_assert_file in
  try
    Stream.iter
      (fun line ->
        let b_insert = initial_insert_create line in
        func_insert_map := b_insert :: !func_insert_map;)
      (line_stream_of_channel ic);
    close_in ic
  with e ->
    close_in ic;
    raise e

let create_print_list () =
  let ic = open_in print_file in
  try
    Stream.iter
      (fun line ->
        print_list := line :: !print_list;)
      (line_stream_of_channel ic);
    close_in ic
  with e ->
    close_in ic;
    raise e

let convert_duet () =
  TranslateCS.convert_cs ();
  let func_list = TranslateCS.get_funcs () in
  let oc = open_out cfg_out_file in
  TranslateCS.print_functions oc;
  close_out oc;
  let glos = TranslateCS.get_globs () in
  create_print_list ();
  create_assume_assert_list ();
  glob_map := List.map convert_global glos;
  fvars := List.map create_func_var func_list;
  let duet_func_list = List.map convert_funcs func_list in
  tmp_file := {!tmp_file with funcs=duet_func_list};
  let main = TranslateCS.get_main () in
  let main_var = List.assoc main.fname !fvars in
  let vinfo_main = fst main_var in
  tmp_file := {!tmp_file with entry_points=[vinfo_main]};
  !tmp_file
