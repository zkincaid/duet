open Printf
open Ocamlbuild_plugin;;

let mkcamlp4 prod deps =
  let mode = match Pathname.get_extension (Pathname.mk prod) with
  | "byte" -> `Byte
  | "native" -> `Native
  | _ -> failwith "mkcamlp4 can build only .byte and .native targets"
  in
  let ocaml = match mode with `Byte -> !Options.ocamlc | `Native -> !Options.ocamlopt in
  let cm name = A (name ^ match mode with `Byte -> ".cmo" | `Native -> ".cmx") in

  rule (sprintf "mkcamlp4 %s" prod) ~deps ~prod begin fun _ _ ->
    Cmd (S[
      ocaml; 
      A "-linkall";
      T(tags_of_pathname prod++"link");
      cm "Camlp4Parsers/Camlp4OCamlRevisedParser";
      cm "Camlp4Parsers/Camlp4OCamlParser";
      cm "Camlp4Printers/Camlp4AutoPrinter";
      Command.atomize_paths deps;
      A"-o"; A prod;
      cm "Camlp4Bin"; 
    ])
  end

let _ =  dispatch begin function
  | After_rules ->
      flag ["pp"; "camlp4of"] & S[A"-loc"; A"loc"];
      flag ["pp"; "camlp4orf"] & S[A"-loc"; A"loc"];
      flag ["ocaml";"pp";"pa_deriving"] (P"pa_deriving.cma");
      dep ["pa_deriving"] ["pa_deriving.cma"];

      ocaml_lib "deriving";

      mkcamlp4 "deriving.byte" ["pa_deriving.cma"];
      mkcamlp4 "deriving.native" ["pa_deriving.cmxa"];

 | _ -> ()
 end;;

