open InterIR
open CfgIr
open Core
open Printf
open String

(* The globals and maps needed for this code *)
let tmp_file = ref {filename="tmp";threads=[];funcs=[];entry_points=[];vars=[];types=[];globinit=None}
let glob_map = ref []
let fvars = ref []
let freturns = ref []
let print_list = ref []
let current_loc_map = ref []
let current_arg_map = ref []
let print_file = "print.txt"


(* Convert the types *)
let rec convert_type t =
  match t with
    InterIR.Int(s) -> Concrete(Int(s))
  | _ -> raise (Unexpected_value ("Found non-integer type:"))


(*Convert the global variables *)
let convert_global (name,typ) =
  let v_type = convert_type typ in
  (name, mk_global_var !tmp_file name v_type)

(*Convert the local variables *)
let convert_local fname (name,typ) =
  let v_type = convert_type typ in
  (name, mk_local_var fname name v_type)

(*Given a variable, get the ICRA variable object *)
let get_var (name,_) =
  if (List.mem_assoc name !current_loc_map) then
    List.assoc name !current_loc_map
  else
    if (List.mem_assoc name !current_arg_map) then
      List.assoc name !current_arg_map
    else
      List.assoc name !glob_map
(*Convert values*)
let get_lvalue_var v=
  match v with
  | InterIR.Var(name, typ) ->get_var (name,typ)
  |Undef -> raise (Unexpected_value ("Unexpected undef in left side of assignment"))
  | _ -> raise (Unexpected_value ("Found field access"))

 let get_lvalue_var_opt v=
  match v with
  | InterIR.Var(name, typ) ->Some(get_var (name,typ))
  |Undef -> None
  | _ -> raise (Unexpected_value ("Found field access"))

let get_lvalue v =
  match v with
  | InterIR.Var(name, typ) -> AccessPath(Variable(get_var (name,typ)))
  |Undef -> Core.Havoc(Core.Concrete (Int(4)))
  | _ -> raise (Unexpected_value ("Found field access"))

let is_boolean_op (binop : InterIR.binop)=
  match binop with
  | GTE -> true
  | GT -> true
  | LTE ->true
  | LT ->true
  | NE -> true
  | EQ -> true
  | And -> true
  | Or -> true
  | _ -> false

(*Converts IR binops to ICRA binops*)
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
  | _ -> raise (Unexpected_value ("Logical operator found in binary expression"))

let convert_unop (unop : InterIR.unop) =
  match unop with
    InterIR.UNeg -> Core.Neg
  | InterIR.LNeg -> Core.BNot

(*
  Converts IR conditional ops to ICRA conditional ops
  ICRA has no GT or GTE ops, to if those occur that op needs to be flipped
 *)
let convert_cop op =
  match op with
    GTE -> (Core.Le, true)
  | GT -> (Core.Lt, true)
  | LTE -> (Core.Le, false)
  | LT -> (Core.Lt, false)
  | NE -> (Core.Ne, false)
  | EQ -> (Core.Eq, false)
  | _ -> raise (Unexpected_value ("Arithmetic operator found in binary expressionn"))

(*Given a type, get it's size.  We only have ints and pointers, so size is 4 or 8*)
let get_type_size typ =
  match typ with
  | InterIR.Int(s) -> Core.Constant(CInt(s,4))
  | _ -> raise (Unexpected_value ("Found non-integer type:"))

(*Converts the rexpr into ICRA expressions*)
let rec convert_rexpr ls =
  match ls with
    InterIR.Constant(x,s) -> Constant(CInt(x,s))
  | InterIR.LVal(v) -> get_lvalue v
  | InterIR.UExpr(op,v) -> let sub_val = convert_rexpr v in
                           let op2 = convert_unop op in
                           Core.UnaryOp(op2,sub_val,Core.Concrete(Int(4)))
  | InterIR.BExpr(l,op,r) ->if (is_boolean_op op) then
                              Core.BoolExpr(convert_bexpr ls)
                            else
                              let l_val = convert_rexpr l in
                              let r_val = convert_rexpr r in
                              let bop = convert_binop op in
                              Core.BinaryOp(l_val,bop,r_val,Core.Concrete(Int(4)))
  | Multiple(_) -> raise (Unexpected_value ("Found multiple. It should have been flattened at this point"))
  and
    convert_bexpr rexpr=
    match rexpr with
      InterIR.BExpr(l,cop,r)->( match cop with
                                 InterIR.And -> Core.And(convert_bexpr l, convert_bexpr r)
                               | InterIR.Or -> Core.Or(convert_bexpr l, convert_bexpr r)
                               | _ -> let (op,switch) = convert_cop cop in
                                      if switch then
                                        Core.Atom(op,convert_rexpr r,convert_rexpr l)
                                      else
                                        Core.Atom(op,convert_rexpr l,convert_rexpr r)
                             )
    | _ ->  raise (Unexpected_value ("Condition has not a boolean type"))


let convert_cond cond :Core.bexpr=
  match cond with
    Jmp -> Core.Bexpr.ktrue
  | NonDet -> Core.Bexpr.ktrue
  | Cond(rexpr) -> convert_bexpr rexpr


(* functions for dealing with return values *)
let create_func_return_vars  { funname ; fargs; flocs; fbody; frets}=
  let create_fun_return_var (name,ty) = mk_global_var !tmp_file (funname^name) (convert_type ty) in
  (funname, List.map create_fun_return_var frets)

let make_caller_ret_assignment accum l_ret global=
  match get_lvalue_var_opt l_ret with
    Some(l_var) -> Core.Def.mk (Assign(l_var, AccessPath(Variable(global)))):: accum
  | None -> accum

let make_ret_assignment cfg global ret_var=
  let duet_return_var=get_lvalue (InterIR.Var ret_var) in
  CfgBuilder.mk_single cfg (Core.Def.mk (Assign(global,duet_return_var)))

(* Converts instructions into ICRA weights to put on edges*)
let convert_insts (inst : inst) =
  match inst with
    Assign(l,r) -> let l_var = get_lvalue_var l in
                   let r_val = convert_rexpr r in
                   [Core.Def.mk (Assign(l_var, r_val))]
  | Assume(cond) -> [Core.Def.mk (Assume (convert_cond cond))]
  | Tick(v) -> raise (Unexpected_value ("Unexpected tick instruction"))
  | Call(a,name,args) ->
     let func_var = Core.AddrOf(Variable(List.assoc name !fvars)) in
     match a with
       [] ->    [Core.Def.mk (Call(None,func_var,List.map convert_rexpr args))]
     | [one] ->    [Core.Def.mk (Call(get_lvalue_var_opt one,func_var,List.map convert_rexpr args))]
     | rets ->let return_assignments= List.fold_left2 make_caller_ret_assignment [] rets (List.assoc name !freturns) in
              (Core.Def.mk (Call(None,func_var,List.map convert_rexpr args))):: return_assignments

(*Make a single point to start off the function*)
let mk_pt dfunc inst =
  let def = convert_insts inst in
  List.map (CfgBuilder.mk_single dfunc.cfg) def


(*For each function, convert into an ICRA cfg*)

let convert_funcs cs_func =
  let blist = cs_func.fbody in
  Printf.eprintf "converting function %s\n" cs_func.funname;
  let duet_func =
    { CfgIr.fname = fst (List.assoc cs_func.funname !fvars);
      CfgIr.formals = [];
      CfgIr.locals = [];
      CfgIr.cfg = CfgIr.Cfg.create ();
      CfgIr.file = Some(!tmp_file) } in
  current_loc_map := [];
  current_arg_map := [];
  let func_convert_local x = convert_local duet_func x in
  current_arg_map := List.map func_convert_local cs_func.fargs;
  current_loc_map := List.map func_convert_local cs_func.flocs;
  (*Get the assume/assert expressions from the list of user inserts*)
  let converted_inserts = [] in
  let (_,arg_list) = List.split !current_arg_map in
  let arg_vars = List.map fst arg_list in
  let duet_func = {duet_func with CfgIr.formals = arg_vars} in
  let init_vertex = Core.Def.mk (Assume (Core.Bexpr.ktrue)) in
  let block_map = ref [] in
  (*Make the first point in the cfg*)
  let mk_func_pt = mk_pt duet_func in
  (*Convert each basic block*)
  Printf.eprintf "converting block \n";
  let convert_blks  x blk =(
      Printf.eprintf "converting block %d\n" x;
      let num_insts = List.length blk.binsts in
      let cfg_insts = (
          if num_insts > 0 then
            List.map mk_func_pt blk.binsts
          else
            [[CfgBuilder.mk_skip duet_func.cfg]]
        ) in
      let mk_t_pt = CfgBuilder.mk_single duet_func.cfg in
      (*Insert the assume/assert expressions at the end of the basic block*)
      let (_,cur_blk_inserts) = List.split (List.filter (function (a,b) -> (a = x)) converted_inserts) in
      let as_pt_lst = List.map mk_t_pt cur_blk_inserts in
      let updated_list = (List.flatten cfg_insts)  @ as_pt_lst in
      (*Create a basic block and add to the basic block map*)
      let cur_block = CfgBuilder.mk_block duet_func.cfg updated_list in
      block_map := !block_map @ [cur_block]
    ) in
  Array.iteri convert_blks  blist;
  Printf.eprintf "making branches \n";
  (*Make an edge from the initial pt to the first pt in the first basic block*)
  let _=CfgBuilder.mk_seq duet_func.cfg (CfgBuilder.mk_single duet_func.cfg init_vertex) (List.hd !block_map) in
  let blk_array = Array.of_list !block_map in
  (*Create edges to connect the blocks*)
  let create_branches x blk = (
      let end_point = blk.btype in
      match end_point with
        Return(ret) -> (
        let ret_point = (match ret with
                           [] -> CfgBuilder.mk_single duet_func.cfg (Core.Def.mk (Return None))
                         | [ret_v] -> CfgBuilder.mk_single duet_func.cfg (Core.Def.mk (Return (Some(get_lvalue (InterIR.Var ret_v)))))
                         | _ -> let return_assignments= List.map2 (make_ret_assignment duet_func.cfg) (List.assoc cs_func.funname !freturns) ret in
                                CfgBuilder.mk_block duet_func.cfg (return_assignments @ [CfgBuilder.mk_single duet_func.cfg (Core.Def.mk (Return None))])
                        ) in
        (*See if their is a print_hull entry for this function in print.txt*)
        let print_hull = List.mem cs_func.funname !print_list in
        let current_blk = Array.get blk_array x in
        (*Create a printbounds variable if the print_hull entry exists*)
        if print_hull then
          begin
            let bvar = get_var ("bytecodecost",Int(4)) in
            let ph = Core.Def.mk (Builtin (PrintBounds bvar)) in
            let ph_pt = CfgBuilder.mk_single duet_func.cfg ph in
            let _=CfgBuilder.mk_seq duet_func.cfg current_blk ph_pt in
            let _=CfgBuilder.mk_seq duet_func.cfg ph_pt ret_point in
            ()
          end
        else(
          let _=CfgBuilder.mk_seq duet_func.cfg current_blk ret_point in
          ()
        )
      )
      | Branch(children) ->
         (
           let condition = blk.bcond in
           match condition with
             Some(Cond(rexpr)) -> (
             let duet_cond=convert_cond (Cond(rexpr)) in
             let current_blk = Array.get blk_array x in
             let then_child = Array.get blk_array (List.hd children) in
             let else_child = Array.get blk_array  (List.hd (List.tl children))  in
             let bthen = CfgBuilder.mk_seq duet_func.cfg (CfgBuilder.mk_single duet_func.cfg (Core.Def.mk (Assume duet_cond))) then_child in
             let belse = CfgBuilder.mk_seq duet_func.cfg (CfgBuilder.mk_single duet_func.cfg (Core.Def.mk (Assume (Core.Bexpr.negate duet_cond)))) else_child in
             let _=CfgBuilder.mk_seq duet_func.cfg current_blk bthen in
             let _=CfgBuilder.mk_seq duet_func.cfg current_blk belse in
             ()
           )
           | _ ->  (
             let current_blk = Array.get blk_array x in
             let connect_children child = (
                 let child_block = Array.get blk_array child in
                 let _=CfgBuilder.mk_seq duet_func.cfg current_blk child_block in
                 ()
               ) in
             List.iter connect_children children; ()
           )
         )
    ) in
  Array.iteri create_branches blist;
  (* CfgIr.Cfg.display duet_func.cfg; *)
  duet_func

let get_fun_type cs_func=
  let ret_vars = cs_func.frets in
  let ret_type = (match ret_vars with
                  | (name,typ)::_ -> convert_type typ
                  | [] -> Core.Concrete(Void)
                 )
  in
  let num_args = List.length cs_func.fargs in
  if num_args = 0 then
    Core.Concrete(Func(ret_type, []))
  else
    let gt_var x = (match x with (name,typ) -> convert_type typ) in
    let type_list = List.map gt_var cs_func.fargs in
    Core.Concrete(Func(ret_type, type_list))

(* Create a function variable for a given function.*)
let create_func_var cs_func =
  let ftype=get_fun_type cs_func in
  (cs_func.funname, mk_global_var !tmp_file cs_func.funname ftype)


(*Creates a output channel for printing  out to intercfg.txt*)
let line_stream_of_channel channel =
  Stream.from
    (fun _ ->
      try Some (input_line channel) with End_of_file -> None);;


(* let initial_insert_create line =
 *   let initial_split = Str.split (Str.regexp_string ";") line in
 *   (List.hd initial_split, List.tl initial_split) *)

(* Reads in lines from assume/assert.txt*)
(* let create_assume_assert_list () =
 *   let ic = open_in assume_assert_file in
 *   try
 *     Stream.iter
 *       (fun line ->
 *         let b_insert = initial_insert_create line in
 *         func_insert_map := b_insert :: !func_insert_map;)
 *       (line_stream_of_channel ic);
 *     close_in ic
 *   with e ->
 *     close_in ic;
 *     raise e *)

(* Reads in lines from print.txt*)
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

(*Top level duet conversion function*)
let parse filename =
  (*Converts for CS project to InterIR*)
  let chan = open_in filename in
  let cs_list = Marshal.from_channel chan in
  close_in chan;
  match cs_list with 
    [func_list,glos,main] -> (
    create_print_list ();
    (*create_assume_assert_list ();*)
    glob_map := List.map convert_global glos;
    fvars := List.map create_func_var func_list;
    freturns := List.map create_func_return_vars func_list;
    Printf.eprintf "converting functions";
    (*Convert each duet function*)
    let duet_func_list = List.map convert_funcs func_list in
    Printf.eprintf "done";
    tmp_file := {!tmp_file with funcs=duet_func_list};
    let main_var = List.assoc main.funname !fvars in
    let vinfo_main = fst main_var in
    (*Create the file object and return in*)
    tmp_file := {!tmp_file with entry_points=[vinfo_main]};
    !tmp_file)
  | _ -> !tmp_file

let _ = CmdLine.register_parser ("cs", parse)
