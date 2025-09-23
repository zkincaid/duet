open Llvm
open Llvm_irreader
open Variable

let llvm_block_to_string (block : llbasicblock) : string =
  let instrs = fold_left_instrs (fun acc instr -> string_of_llvalue instr :: acc) [] block in
  String.concat "\n" (List.rev instrs)

let block_eq b1 b2 = 
  let b1_str = llvm_block_to_string b1 in
  let b2_str = llvm_block_to_string b2 in
  String.equal b1_str b2_str

let block_id (block : llbasicblock) = 
  let func = block_parent block in 
  let entry = entry_block func in
  if block_eq entry block then 0 else (
  let block_str = string_of_llvalue (value_of_block block) |> String.trim |> String.split_on_char ' ' |> List.hd in
  let id_str = String.sub block_str 0 (String.length block_str - 1) in
  int_of_string id_str)
      

let print_llvm_block (block : llbasicblock) : unit =
  print_string "\n Block begin:";
  iter_instrs (fun instr -> print_string "\n Instr:"; print_string (string_of_llvalue instr)) block;
  print_string "\n Block end\n"


module LlvmNode = struct 
  (* [fst t] is the LLVM label. [snd t] distinguishes between duplicated phi nodes, and should be 0 if it is not a phi node. *)
    type t = int * int * llbasicblock
    let compare (l, p, _) (l', p', _) = if Int.compare l l' != 0 then Int.compare l l' else Int.compare p p'
    let equal (l, p, _) (l', p', _)  = Int.equal l l' && Int.equal p p'
    let hash a = Hashtbl.hash a
    let name (l, p, _) = let l_str = if (l = (-1)) then "ret" else string_of_int l in 
      if p = 0 then l_str else "phi"^l_str^"_"^(string_of_int p)
    let llvm_identifier (x, _, _ : t) = x
    let llvm_block (_, _, block : t) = block
    let phi_num (_, p, _) = p
end

let dummy_block =
  let ctx = Llvm.global_context () in
  let llmod = Llvm.create_module ctx "dummy_module" in
  let i32t = Llvm.i32_type ctx in
  let fn_ty = Llvm.function_type i32t [||] in
  let fn = Llvm.define_function "dummy_fn" fn_ty llmod in
  Llvm.append_block ctx "dummy_block" fn

let dummy = (-1, 0, dummy_block)


module LlvmGraph = Graph.Persistent.Digraph.Concrete(LlvmNode)


let generate_llvm_ir c_file =
  let ctx = (create_context ()) in 
  let llvm_ir_file_unoptimized = Filename.temp_file "output" ".ll" in
  let llvm_ir_file_optimized = Filename.temp_file "output_o" ".ll" in
  let clang_command = Printf.sprintf "clang -Xclang -disable-O0-optnone -O0 -emit-llvm -S %s -o %s" c_file llvm_ir_file_unoptimized in
  let opt_command = Printf.sprintf "opt -passes mem2reg -S %s -o %s" llvm_ir_file_unoptimized llvm_ir_file_optimized in
  let _ = Sys.command clang_command in
  let _ = Sys.command opt_command in

  (* HACKY: Homebrew clang sometimes emits malformed LLVM IR files, 
      placing the nuw (no unsigned wrap) keyword in the getelementptr instruction 
      when nuw should only be used for integer arithmetic instructions.
      We solve this by deleting the nuw keyword. This doesn't affect our 
      translation because we don't consider integer wrapping in our translation in any case
  *)
  let content = In_channel.with_open_bin llvm_ir_file_optimized In_channel.input_all in
  let content' = Str.global_replace (Str.regexp "getelementptr inbounds nuw ") "getelementptr inbounds " content in
  Out_channel.with_open_bin llvm_ir_file_optimized (fun oc ->
      Out_channel.output_string oc content'
    );

  let mem_buffer = MemoryBuffer.of_file llvm_ir_file_optimized in
  parse_ir ctx mem_buffer

(* A phi node is a LlvmNode where some outgoing edge has a phi instruction in it. 
LIMITATION: we currently only handle phi nodes which have only one outgoing edge and which only contain one phi instruction. 
This transformation duplicates the phi node, replaces the phi instruction with the relevant set, and fixes the predecessor edges.
*)
let duplicate_phi_nodes (g : LlvmGraph.t) : LlvmGraph.t = 
  let phi_nodes = LlvmGraph.fold_vertex (fun (id, phi_id, block) acc ->
    let has_phi = fold_left_instrs (fun acc instr -> 
      match instr_opcode instr with
      | Opcode.PHI -> (if acc then (print_string "Warning: multiple phi statements in block. No checking implemented yet."; true) else true) 
      | _ -> acc      
      ) false block in
    if has_phi then (id, phi_id, block) :: acc else acc 
  ) g [] in 
  List.fold_left (fun g phi_node ->
    let with_new_edges, _ = LlvmGraph.fold_pred (fun pred (g, phi_id) ->
        let id, _, block = phi_node in 
        let with_out_edges = LlvmGraph.fold_succ (fun succ g -> LlvmGraph.add_edge g (id, phi_id, block) succ) g phi_node g in 
        LlvmGraph.add_edge with_out_edges pred (id, phi_id, block), phi_id + 1
      ) g phi_node (g, 1) in 
      LlvmGraph.remove_vertex with_new_edges phi_node
    ) g phi_nodes

let generate_llvm_graph_from_ir m = 
  (* For now, we require that the input is a single function. *)
  let funcs = fold_left_functions (fun acc func -> 
    match acc with 
    | [] -> [func]
    | _ -> print_string "Warning: multiple functions in LLVM IR. Only the first function will be used"; print_string (string_of_llvalue func); acc
  ) [] m in
  let func = List.hd funcs in 

  let params = fold_left_params (fun acc param -> 
    let param_str = string_of_llvalue param in
    let header = String.sub param_str 0 4 in
    let name = String.sub param_str 4 (String.length param_str - 4) in
    if (header = "ptr ") then 
      let pvar = new_pvar name in
      (Pointer pvar) :: acc
    else if (header = "i32 ") then 
      let var = new_var name in 
      (Variable var) :: acc 
    else 
      raise (Failure "Unknown parameter type")
    ) [] func in 

  (* The entry is the first block of this function that the LLVM module returns *)
  let g = fold_left_blocks (fun g block -> 
    let g' = LlvmGraph.add_vertex g (block_id block, 0, block) in 
    match block_terminator block with
    | None -> g'
    | Some terminator -> 
      fold_successors (fun succ g' -> 
        LlvmGraph.add_edge g' (block_id block, 0, block) (block_id succ, 0, succ)) terminator g'
    ) LlvmGraph.empty func 
  |> duplicate_phi_nodes in 
  
  g, (0, 0, entry_block func), params

let generate_llvm_graph c_file = generate_llvm_graph_from_ir (generate_llvm_ir c_file)

let string_contains str contains = 
  String.fold_left (fun acc c -> 
    if acc = "" then acc else 
    if c = (String.get acc 0) then String.sub acc 1 (String.length acc - 1) else contains) contains str = ""

let is_malloc (instr : llvalue) : bool = 
  let instr_str = string_of_llvalue instr |> String.trim in
  string_contains instr_str "malloc"

let is_free (instr : llvalue) : bool = 
  let instr_str = string_of_llvalue instr |> String.trim in
  string_contains instr_str "free"