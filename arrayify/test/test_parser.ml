open Arrayify
open Boogie_driver  (* your parser entry point *)

let () =
  if Array.length Sys.argv < 2 then (
    Printf.eprintf "Usage: %s <file.bpl>\n" Sys.argv.(0);
    exit 1
  );

  let filename = Sys.argv.(1) in
  let prog = parse filename in   (* parse returns boogie_instr list *)

  print_string (Boogie_ast.string_of_program prog);  (* Print the parsed program *)
  
