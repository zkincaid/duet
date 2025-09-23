open Symbolicheap
open Llvmutil
open Boogieir
open Llvm
open Variable
module LlvmGraph = Graph.Persistent.Digraph.Concrete(LlvmNode)
module BGraph = Boogieir.BGraph

module LLvmNodeSet = Set.Make(LlvmNode)
module Heap = Set.Make(HeapElem)

let extract_int_term (v : llvalue) : int_term = 
  let s = string_of_llvalue v |> String.trim in 
  if ((String.sub s 0 4) = "i32 ") then 
    (
      let value_str = String.sub s 4 (String.length s - 4) in
      if String.get value_str 0 = '%' then Var (new_var value_str) 
        else Int (String.sub s 4 (String.length s - 4) |> int_of_string)
    ) else 
  if ((String.sub s 0 4) = "i64 ") then 
    (
    let value_str = String.sub s 4 (String.length s - 4) in
    if String.get value_str 0 = '%' then Var (new_var value_str) 
      else Int (String.sub s 4 (String.length s - 4) |> int_of_string)
    ) else 
  if ((String.sub s 0 3) = "i8 ") then 
    (
    let value_str = String.sub s 3 (String.length s - 3) in
    if String.get value_str 0 = '%' then Var (new_var value_str) 
      else Int (String.sub s 3 (String.length s - 3) |> int_of_string)
    ) else
  if (String.get s 0 = '%') then (
      let var_name = s |> String.trim |> String.split_on_char ' ' |> List.hd in
      let var = new_var var_name in
      Var var
  ) else 
    raise (Failure "unimplemented int term extraction")

let extract_pointer (v : llvalue) : pvar = 
  let s = string_of_llvalue v |> String.trim in 
  if ((String.sub s 0 4) = "ptr ") then 
    (
      new_pvar (String.sub s 4 (String.length s - 4)) 
    ) else if (String.get s 0 = '%') then 
      (let pvar_name = s |> String.trim |> String.split_on_char ' ' |> List.hd in
      new_pvar pvar_name) 
  else (raise (Failure "unimplemented pointer extraction"))

let extract_target (v : llvalue) : string = 
  string_of_llvalue v |> String.trim |> String.split_on_char ' ' |> List.hd

let symbolic_update_instr (instr : llvalue) (cond : symbolicheap) (phi_num : int) (bgraph : BGraph.t) : symbolicheap * boogie_instr list = 
  match instr_opcode instr with 
    | 	Opcode.Invalid -> raise (Failure "Not implemented") 	(*	
    Not an instruction
      *)
    | 	Opcode.Ret -> (
      if num_operands instr = 0 then 
        cond, []
    else 
      let term = operand instr 0 |> extract_int_term in
      let boogie_instrs = [
        Return (boogie_term_of_int_term term);
      ]  in 
      cond, boogie_instrs
    ) (*	
    Terminator Instructions
      *)
    | 	Opcode.Br -> cond, []
    | 	Opcode.Switch -> raise (Failure "Not implemented")
    | 	Opcode.IndirectBr -> raise (Failure "Not implemented")
    | 	Opcode.Invoke -> raise (Failure "Not implemented")
    | 	Opcode.Invalid2 -> raise (Failure "Not implemented")
    | 	Opcode.Unreachable -> raise (Failure "Not implemented")
    | 	Opcode.Add  -> (
      let tgt = extract_target instr in
      let tgt_var = new_var tgt in  
      let left = operand instr 0 |> extract_int_term in
      let right = operand instr 1 |> extract_int_term in
      let term = Symbolicheap.Add (left, right) in
      let boogie_instrs = [
        Assign (boogie_var_of_var tgt_var, boogie_term_of_int_term term);
      ]  in
      let f, h = (quantify_out_var cond tgt_var) in
      let postcond = Symbolicheap.And (Eq (Var tgt_var, term), f), h in
      postcond, boogie_instrs

    )	(*	
    Standard Binary Operators
      *)
    | 	Opcode.FAdd -> raise (Failure "Not implemented")
    | 	Opcode.Sub -> (
      let p0 = operand instr 0 |> extract_int_term in
      let p1 = operand instr 1 |> extract_int_term in
      let tgt = extract_target instr in
      let tgt_var = new_var tgt in
      let f, h = (quantify_out_var cond tgt_var) in
      let postcond = Symbolicheap.And ((Symbolicheap.Eq ((Var tgt_var),(Symbolicheap.Sub (p0, p1) ))), f), h in 
      let boogie_instrs = [
        Assign (boogie_var_of_var tgt_var, boogie_term_of_int_term (Symbolicheap.Sub (p0, p1)));
      ] in
      postcond, boogie_instrs)
    | 	Opcode.FSub -> raise (Failure "Not implemented")
    | 	Opcode.Mul -> raise (Failure "Not implemented")
    | 	Opcode.FMul -> raise (Failure "Not implemented")
    | 	Opcode.UDiv -> raise (Failure "Not implemented")
    | 	Opcode.SDiv -> raise (Failure "Not implemented")
    | 	Opcode.FDiv -> raise (Failure "Not implemented")
    | 	Opcode.URem -> raise (Failure "Not implemented")
    | 	Opcode.SRem -> raise (Failure "Not implemented")
    | 	Opcode.FRem -> raise (Failure "Not implemented")
    | 	Opcode.Shl  -> raise (Failure "Not implemented")	(*	
    Logical Operators
      *)
    | 	Opcode.LShr -> raise (Failure "Not implemented")
    | 	Opcode.AShr -> raise (Failure "Not implemented")
    | 	Opcode.And -> raise (Failure "Not implemented")
    | 	Opcode.Or -> raise (Failure "Not implemented")
    | 	Opcode.Xor -> raise (Failure "Not implemented")
    | 	Opcode.Alloca  -> raise (Failure "Not implemented")	(*	
    Memory Operators
      *)
    | 	Opcode.Load -> (
      let pointer = operand instr 0 |> extract_pointer in
      let tgt = extract_target instr in
      let tgt_var = new_var tgt in
      match sheap_single_b cond pointer with 
      | Some b -> (
        let boogie_instrs = [
                        Assert (Leq (Int 0, Var (boogie_var_of_pvar pointer))); 
                        Assert (Not (Leq (Var (boogie_length_of_boogie_avar (boogie_avar_of_bvar b)), Var (boogie_var_of_pvar pointer)))); 
                        Assign ((boogie_var_of_var tgt_var), (Read ((boogie_avar_of_bvar b),(Var (boogie_var_of_pvar pointer)))))
                      ] in 
                        cond, boogie_instrs
      )
      | None -> (
        let boogie_instrs = [ Assert (Not (True))] in 
                      true_sheap, boogie_instrs
      )
    )
    | 	Opcode.Store -> (let value = operand instr 0 |> extract_int_term in 
                    let pointer_pvar = extract_pointer (operand instr 1) in 
                    match sheap_single_b cond pointer_pvar with 
                    | Some b -> let boogie_instrs = [
                        Assert (Leq (Int 0, Var (boogie_var_of_pvar pointer_pvar))); 
                        Assert (Leq (Var (boogie_var_of_pvar pointer_pvar), Var (boogie_length_of_boogie_avar (boogie_avar_of_bvar b)))); 
                        AWrite (boogie_avar_of_bvar b, Var (boogie_var_of_pvar pointer_pvar), boogie_term_of_int_term value)
                      ] in 
                        cond, boogie_instrs
                    | None -> (
                      let boogie_instrs = [ Assert (Not (True))] in 
                      true_sheap, boogie_instrs
                    )
                    )
    | 	Opcode.GetElementPtr -> (
      let pointer = operand instr 0 |> extract_pointer in
      let offset = operand instr 1 |> extract_int_term in
      let tgt = extract_target instr in
      let tgt_var = new_pvar tgt in
      let boogie_instrs = [
        Assign (boogie_var_of_pvar tgt_var, Sum (boogie_term_of_pointer_term (Pointer pointer), boogie_term_of_int_term offset));
      ] in
      let f, h = (quantify_out_pvar cond tgt_var) in
      let postcond = Symbolicheap.And ((pt_eq (Pointer tgt_var) (PointerSum (Pointer pointer, offset))), f), h in 
      postcond, boogie_instrs)
    | 	Opcode.Trunc -> (
      let v = operand instr 0 |> extract_int_term in
      let tgt = extract_target instr in
      let tgt_var = new_var tgt in
      let boogie_instrs = [
        Assign (boogie_var_of_var tgt_var, boogie_term_of_int_term v);
      ] in
      let f, h = (quantify_out_var cond tgt_var) in
      let postcond = Symbolicheap.And (Eq (Var tgt_var, v), f), h in
      postcond, boogie_instrs
    ) 	(*	
    Cast Operators
      *)
    | 	Opcode.ZExt -> raise (Failure "Not implemented")
    | 	Opcode.SExt -> raise (Failure "Not implemented")
    | 	Opcode.FPToUI -> raise (Failure "Not implemented")
    | 	Opcode.FPToSI -> raise (Failure "Not implemented")
    | 	Opcode.UIToFP -> raise (Failure "Not implemented")
    | 	Opcode.SIToFP -> raise (Failure "Not implemented")
    | 	Opcode.FPTrunc -> raise (Failure "Not implemented")
    | 	Opcode.FPExt -> raise (Failure "Not implemented")
    | 	Opcode.PtrToInt -> (
      let pointer = operand instr 0 |> extract_pointer in
      let tgt = extract_target instr in
      let tgt_var = new_var tgt in
      let boogie_instrs = [
        Assign (boogie_var_of_var tgt_var, boogie_term_of_pointer_term (Pointer pointer));
      ] in
      let f, h = (quantify_out_var cond tgt_var) in
      let postcond = Symbolicheap.And ((Symbolicheap.Eq ((Offset (Pointer pointer)), (Var tgt_var))), f), h in 
      postcond, boogie_instrs)
    | 	Opcode.IntToPtr -> raise (Failure "Not implemented")
    | 	Opcode.BitCast -> raise (Failure "Not implemented")
    | 	Opcode.ICmp  -> (
      let lhs = operand instr 0 |> extract_int_term in
      let rhs = operand instr 1 |> extract_int_term in
      (* This is a hacky way of extracting the variable that a operation assigns to. *)
      let cmp_flag_name = string_of_llvalue instr |> String.trim |> String.split_on_char ' ' |> List.hd in 
      let cmp_flag = new_var cmp_flag_name in 
      let op, bop = match icmp_predicate instr with 
        | Some Llvm.Icmp.Eq -> Symbolicheap.Eq (lhs, rhs), Eq (boogie_term_of_int_term lhs, boogie_term_of_int_term rhs)
        | Some Llvm.Icmp.Ne -> Not (Eq (lhs, rhs)), Not (Eq (boogie_term_of_int_term lhs, boogie_term_of_int_term rhs))
        | Some Llvm.Icmp.Sgt -> Not (Leq (lhs, rhs)), Not (Leq (boogie_term_of_int_term lhs, boogie_term_of_int_term rhs))
        | Some Llvm.Icmp.Sge -> Leq (rhs, lhs), Leq (boogie_term_of_int_term rhs, boogie_term_of_int_term lhs)
        | Some Llvm.Icmp.Slt -> Not (Leq (rhs, lhs)), Not (Leq (boogie_term_of_int_term rhs, boogie_term_of_int_term lhs))
        | Some Llvm.Icmp.Sle -> Leq (lhs, rhs),  Leq (boogie_term_of_int_term lhs, boogie_term_of_int_term rhs)
        | _ -> print_string ((string_of_llvalue instr)); raise (Failure "Not implemented")
      in
      let boogie_instrs = [
        IteAssign ((boogie_var_of_var cmp_flag), bop, Int 1, Int 0);
      ]
      in
      let f, h = (quantify_out_var cond cmp_flag) in
      let op_or_not_op = Symbolicheap.Or (And (op, Eq (Var cmp_flag, Int 1)), And (Not op, Eq (Var cmp_flag, Int 0))) in  
      let postcond = Symbolicheap.And (op_or_not_op, f), h in 
      postcond, boogie_instrs
)
        (*	
    Other Operators
      *)
    | 	Opcode.FCmp -> raise (Failure "Not implemented")
    | 	Opcode.PHI -> (
        let tokens = string_of_llvalue instr |> String.trim |> String.split_on_char ' ' in 
        let type_defn = List.nth tokens 3 in 
        if type_defn = "i32" then (
        let term = operand instr (phi_num - 1) |> extract_int_term in 
        let tgt = extract_target instr in
        let tgt_var = new_var tgt in
        let boogie_instrs = [
          Assign (boogie_var_of_var tgt_var, boogie_term_of_int_term term);
        ]  in 
        let f, h = (quantify_out_var cond tgt_var) in
        let postcond = Symbolicheap.And (Eq (Var tgt_var, term), f), h in
         postcond, boogie_instrs) 
        else if type_defn = "ptr" then (
          let ptr = operand instr (phi_num - 1) |> extract_pointer in 
          let tgt = extract_target instr in 
          let tgt_ptr = new_pvar tgt in 
          let boogie_instrs = [
            Assign (boogie_var_of_pvar tgt_ptr, boogie_term_of_pointer_term (Pointer ptr))
          ] in 
          let f, h = (quantify_out_pvar cond tgt_ptr) in
          let postcond = Symbolicheap.And (
            Symbolicheap.And (
              BlockEq (Block (Pointer ptr), Block (Pointer tgt_ptr)),
              Eq (Offset (Pointer ptr), Offset (Pointer tgt_ptr))), f), h in 
          postcond, boogie_instrs
        ) else (raise (Failure "unknown phi type defn"))
        )
    | 	Opcode.Call -> (
      if is_malloc instr then (
        let size = operand instr 0 |> extract_int_term in 
        let new_bvar = Boogieir.generate_new_bvar bgraph in 
        let tgt = extract_target instr in
        let tgt_var = new_pvar tgt in
        let boogie_instrs = [
          AAssign (boogie_avar_of_bvar new_bvar, boogie_avar_of_bvar new_bvar);
          Assign (boogie_length_of_boogie_avar (boogie_avar_of_bvar new_bvar), boogie_term_of_int_term size);
          Assign (boogie_var_of_pvar tgt_var, Int 0);          
        ] in
        let f, h = (quantify_out_pvar cond tgt_var) in
        let post_f = Symbolicheap.And ((BlockEq ((Block (Pointer tgt_var)), (BVar new_bvar))), Symbolicheap.And (Eq (Offset (Pointer tgt_var), Int 0), f)) in
        (post_f, (Heap.add (Array new_bvar) h)), boogie_instrs
      ) else if is_free instr then (
         let pointer = operand instr 0 |> extract_pointer in
         match sheap_single_b cond pointer with
         | Some b -> (let f, h = cond in (f, Heap.remove (Array b) h), [])
         | None -> (cond, [Assert (Not (True))]) (* assert false because we're freeing a pointer that is not pointing to a single heap element*)      
      )  
      else raise (Failure "Not implemented")

    
    )
    | 	Opcode.Select -> raise (Failure "Not implemented")
    | 	Opcode.UserOp1 -> raise (Failure "Not implemented")
    | 	Opcode.UserOp2 -> raise (Failure "Not implemented")
    | 	Opcode.VAArg -> raise (Failure "Not implemented")
    | 	Opcode.ExtractElement -> raise (Failure "Not implemented")
    | 	Opcode.InsertElement -> raise (Failure "Not implemented")
    | 	Opcode.ShuffleVector -> raise (Failure "Not implemented")
    | 	Opcode.ExtractValue -> raise (Failure "Not implemented")
    | 	Opcode.InsertValue -> raise (Failure "Not implemented")
    | 	Opcode.Fence -> raise (Failure "Not implemented")
    | 	Opcode.AtomicCmpXchg -> raise (Failure "Not implemented")
    | 	Opcode.AtomicRMW -> raise (Failure "Not implemented")
    | 	Opcode.Resume -> raise (Failure "Not implemented")
    | 	Opcode.LandingPad -> raise (Failure "Not implemented")
    |   _ -> raise (Failure "Not implemented")


(* If Llvm basic block [weight] is executed from state [precondition], the output (postcondition, instrs) should be the post state [postcondition] and the equivalent translation in Boogie [instrs] *)
let symbolic_update (src : LlvmNode.t) (precondition : symbolicheap) (bgraph : BGraph.t) : symbolicheap * boogie_instr list = 
  fold_left_instrs (fun (cond, blist) instr -> let post, boogie_translation = symbolic_update_instr instr cond (LlvmNode.phi_num src) bgraph in post, (blist @ boogie_translation)) (precondition, []) (LlvmNode.llvm_block src) 

(* Given a state [postcondition], computes most precise widening in finite class *)
let widen (f, h : symbolicheap) : symbolicheap = 
  let peqs = pointer_equalities (f, h) in
  let f' = List.fold_left (fun acc (p, b) -> Symbolicheap.And (Symbolicheap.BlockEq ((Block (Pointer p)), (BVar b)), acc)) Symbolicheap.True peqs in
  let h' = List.fold_left (fun acc (_, b) -> Heap.add (Array b) acc) Heap.empty peqs in 
  let h' = if Heap.exists (fun e -> not (Heap.mem e h')) h then (Heap.add TrueHeap h') else (h') in 
  f', h'

(* Checks if [from] entails [towards] up to arbitrary permutation of the block variables. Returns None if not, or otherwise Some (to, instrs) where instrs encodes the permutation in Boogie *)
let check_rotate_entails (from : symbolicheap) (towards : symbolicheap) : (boogie_instr list) option = 
  if not (sheap_equals towards (widen towards)) then None else
  let from_peqs = pointer_equalities from in
  let towards_peqs = pointer_equalities towards in
  let rotation = List.fold_left (fun acc (p, b) -> 
    match acc with 
    | Some instrs -> (
      match List.assoc_opt p from_peqs with 
      | Some b' -> Some (if (b = b') then instrs else ((boogie_avar_of_bvar b', boogie_avar_of_bvar b) :: instrs))
      | None -> None
    ) 
    | None -> None
    ) (Some []) towards_peqs in 
  match rotation with 
  | Some ls -> 
    let dedup, err = List.fold_left (fun (acc, err) (from, towards) -> 
      match List.assoc_opt from acc with 
      | Some towards' -> if towards = towards' then acc, err else acc, true
      | None -> (from, towards) :: acc, err) ([], false) ls in 
      if err then None else Some [Rotate dedup]
  | None -> None

let gen_boogie_edge (from : BGNode.t) (towards : BGNode.t) (rotation : boogie_instr list option) : BGEdge.t = 
  let (_, from_node, _, _) = from in 
  let (_, towards_node, _, _) = towards in
  match block_terminator (LlvmNode.llvm_block from_node) with
  | None -> None, rotation
  | Some terminator -> if (is_conditional terminator) then 
  (
    match get_branch terminator with 
    | Some (`Conditional (_, taken_block, not_taken_block)) -> (
      let cmp_flag_name = (string_of_llvalue terminator |> String.trim |> String.split_on_char ' ' |> List.nth) 2 in 
            let cmp_flag_name = String.sub cmp_flag_name 0 (String.length cmp_flag_name - 1) in
            let cmp_flag = new_var cmp_flag_name in
            let branch_condition = if (Llvmutil.block_eq (LlvmNode.llvm_block towards_node) (taken_block)) then ((Eq (Var (boogie_var_of_var cmp_flag), Int 1))) 
            else (if (Llvmutil.block_eq (LlvmNode.llvm_block towards_node) not_taken_block) then ((Eq (Var (boogie_var_of_var cmp_flag), Int 0))) 
            else (raise (Failure "towards not in branch statement"))) in 
      Some branch_condition, rotation
    )
    | Some (`Unconditional _) -> None, rotation
    | None -> raise (Failure "Not implemented")
  )
  else (None, rotation) 

let gen_branch_condition (from : LlvmNode.t) (towards : LlvmNode.t) : formula = 
  match block_terminator (LlvmNode.llvm_block from) with 
  | None -> Symbolicheap.True
  | Some terminator -> if (is_conditional terminator) then 
  (
    match get_branch terminator with 
    | Some (`Conditional (_, taken_block, not_taken_block)) -> (
      let cmp_flag_name = (string_of_llvalue terminator |> String.trim |> String.split_on_char ' ' |> List.nth) 2 in 
      let cmp_flag_name = String.sub cmp_flag_name 0 (String.length cmp_flag_name - 1) in
      let cmp_flag = new_var cmp_flag_name in
      let branch_condition = if (Llvmutil.block_eq (LlvmNode.llvm_block towards) (taken_block)) then ((Symbolicheap.Eq (Var cmp_flag, Int 1))) 
      else (if (Llvmutil.block_eq (LlvmNode.llvm_block towards) not_taken_block) then ((Eq (Var cmp_flag, Int 0))) 
      else (raise (Failure "towards not in branch statement"))) in 
      branch_condition
    )
    | Some (`Unconditional _) -> Symbolicheap.True
    | None -> raise (Failure "Not implemented")
  )
  else Symbolicheap.True 


let execute (entry : LlvmNode.t) (graph : LlvmGraph.t) (precondition : symbolicheap) : BGraph.t * BGNode.t = 
  (* For now, widening points will be computed via backedges *) 
   let initial_node = ref None in 
   let rec go worklist bgraph edges = 
    if worklist = [] then bgraph, edges else (
      let (repeat_ct, node, precondition) = List.hd worklist in 
      let worklist = List.tl worklist in
      let post, boogie_instrs = symbolic_update node precondition bgraph in 
      let (replacement_bnode : BGNode.t) = (repeat_ct, node, precondition, boogie_instrs) in 
      if !initial_node = None then initial_node := Some replacement_bnode;
      let bgraph = BGraph.add_vertex bgraph replacement_bnode in
      print_string ("Popping node "^(LlvmNode.name node)^" off worklist\n");
      let worklist, edges = LlvmGraph.fold_succ (fun succ (worklist, edges) ->
        print_string ("Considering edge to "^(LlvmNode.name succ)^"\n");
          let post_with_branch = Symbolicheap.And ((fst post), gen_branch_condition node succ), snd post in
          let new_repeat_ct = BGraph.fold_vertex (fun (r, l, _, _) m -> if LlvmNode.equal l succ then max m (r + 1) else m) bgraph (0) in
          let new_repeat_ct = List.fold_left (fun m (r, l, _) -> if LlvmNode.equal l succ then max m (r + 1) else m) new_repeat_ct worklist in
          if (LlvmNode.compare succ node < 0) then (
            print_string ("Found backedge from "^(LlvmNode.name node)^" to "^(LlvmNode.name succ)^"\n");
            let widened_postcondition = widen post_with_branch in
            let exists_covering_vertex = BGraph.fold_vertex (fun previous_bnode find -> 
              let (_, previous_node, previous_cond, _) = previous_bnode in 
              match (find, LlvmNode.equal previous_node succ) with 
              | (Some _), _ | _, false -> find 
              | None, true -> 
                match check_rotate_entails widened_postcondition previous_cond with 
                | Some rot -> Some (previous_bnode, rot)
                | None -> None
                ) bgraph None in 
            match exists_covering_vertex with 
              | None -> (new_repeat_ct, succ, widened_postcondition) :: worklist, (replacement_bnode, (new_repeat_ct, succ), None) :: edges
              | Some ((r, n, _, _), rotation) -> worklist, (replacement_bnode, (r, n), Some rotation) :: edges 
          ) else (
            (new_repeat_ct, succ, post_with_branch) :: worklist, (replacement_bnode, (new_repeat_ct, succ), None) :: edges
          )
        ) graph node (worklist, edges) in 
      go worklist bgraph edges
    )
      in 
      let bgraph, edges = go [0, entry, precondition] BGraph.empty [] in 

      let initial_node = match !initial_node with 
        | Some node -> node
        | None -> raise (Failure "No initial node found")
    in
      BGraph.fold_vertex (fun bnode bgraph -> 
          let relevant_edges = List.filter (fun e -> let (_, (r, n), _) = e in let (r', n', _, _) = bnode in r = r' && LlvmNode.equal n n') edges in
          List.fold_left (fun bgraph (pred, _, rotation) -> 
              BGraph.add_edge_e bgraph (pred, gen_boogie_edge pred bnode rotation, bnode) 
            ) bgraph relevant_edges
      ) bgraph bgraph,
      initial_node
      
