open Apak
open Patop

include Log.Make(struct let name = "patools" end)
module F = PaFormula
module Smt = PaSmt

let execute cmd f =
  let chan = Unix.open_process_in cmd in
  ignore (Unix.wait ());
  (try
     while true do
       f (input_line chan)
     done
   with End_of_file -> ());
  close_in chan

let z3 file =
  execute
    ("z3 -smt2 " ^ file)
    (fun s -> print_endline s; flush stdout)

let eprover file =
  execute
    ("eprover -tptp3 " ^ file)
    (fun s -> print_endline s; flush stdout)

let load_automaton_cfa filename =
  let open Lexing in
  let lexbuf = Lexing.from_channel (open_in filename) in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  try PaParse.cfa PaLex.token lexbuf with
  | PaParse.Error ->
    let open Lexing in
    let pos = lexbuf.lex_curr_p in
    failwith (Printf.sprintf "Parse error: %s:%d:%d"
                filename
                pos.pos_lnum
                (pos.pos_cnum - pos.pos_bol + 1))

let load_automaton filename =
  let open Lexing in
  if Filename.check_suffix filename "cfa" then
    load_automaton_cfa filename
  else
    let lexbuf = Lexing.from_channel (open_in filename) in
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
    try PaParse.main PaLex.token lexbuf with
    | PaParse.Error ->
      let open Lexing in
      let pos = lexbuf.lex_curr_p in
      failwith (Printf.sprintf "Parse error: %s:%d:%d"
                  filename
                  pos.pos_lnum
                  (pos.pos_cnum - pos.pos_bol + 1))

let load_formula filename =
  let open Lexing in
  let lexbuf = Lexing.from_channel (open_in filename) in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  try
    F.substitute
      (BatPervasives.undefined ~message:"Start formula should be a sentence")
      (PaParse.main_formula PaLex.token lexbuf)
  with
  | PaParse.Error ->
    let open Lexing in
    let pos = lexbuf.lex_curr_p in
    failwith (Printf.sprintf "Parse error: %s:%d:%d"
                filename
                pos.pos_lnum
                (pos.pos_cnum - pos.pos_bol + 1))

let load_word filename =
  let open Lexing in
  let lexbuf = Lexing.from_channel (open_in filename) in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  try PaParse.word PaLex.token lexbuf with
  | PaParse.Error ->
    let open Lexing in
    let pos = lexbuf.lex_curr_p in
    failwith (Printf.sprintf "Parse error: %s:%d:%d"
                filename
                pos.pos_lnum
                (pos.pos_cnum - pos.pos_bol + 1))

let load_structs filename =
  let open Lexing in
  let lexbuf = Lexing.from_channel (open_in filename) in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  try StructParse.main StructLex.token lexbuf with
  | StructParse.Error ->
    let open Lexing in
    let pos = lexbuf.lex_curr_p in
    failwith (Printf.sprintf "Parse error: %s:%d:%d"
                filename
                pos.pos_lnum
                (pos.pos_cnum - pos.pos_bol + 1))

let pp_formula phi = F.pp Format.pp_print_string Format.pp_print_int phi

let bounded_empty = Bounded.bounded_empty

let complement = A.negate

let intersect = A.intersect

let print_post_formula pa phi =
  Alphabet.Set.iter (fun alpha ->
      logf "Post %a:@\n  @[%a@]"
        Format.pp_print_string alpha
        (F.pp Format.pp_print_string Format.pp_print_int)
        (A.post pa phi alpha)
    ) (A.alphabet pa)

let bounded_check_emptiness_certificate pa phi =
  BatEnum.iter (fun config ->
      BatEnum.iter (fun label ->
          BatEnum.iter (fun m ->
              if not (A.Config.models m phi) then begin
                let (alpha,id) = label in
                logf ~attributes:[`Red;`Bold]
                  "Found counter-example to consecution:";
                logf "%a@\n   --( %s : %d )->@\n%a"
                  A.Config.pp config
                  alpha
                  id
                  A.Config.pp m;
                exit (-1)
              end
            ) (A.succs pa config label)
        ) (ApakEnum.cartesian_product
             (Alphabet.Set.enum (A.alphabet pa))
             (A.Config.universe config))
    ) (A.Config.min_models 2 phi)

module Config = A.Config
let model_of_z3 m predicates size =
  let open BatPervasives in
  let open F in
  let open Z3 in
  let open Model.FuncInterp in
  predicates
  /@ (fun (p, k) ->
      if k = 0 then
        match m#get_bool_interp p with
        | Some true -> Config.add p [] (Config.empty size)
        | _ -> Config.empty size
      else
        match m#get_func_interp p with
        | None -> Config.empty 1
        | Some interp ->
          if Smt.bool_val (get_else interp) then begin
            let full =
              BatList.of_enum ((1 -- k) /@ (fun _ -> (1 -- size)))
              |> ApakEnum.tuples 
              |> BatEnum.fold (fun m tuple ->
                  Config.add p tuple m
                ) (Config.empty size)
            in
            (BatList.enum (get_entries interp))
            |> BatEnum.fold (fun m entry ->
                if Smt.bool_val (FuncEntry.get_value entry) then
                  m
                else
                  let tuple = List.map Smt.int_val (FuncEntry.get_args entry) in
                  Config.remove p tuple m
              ) full
          end else begin
            (BatList.enum (get_entries interp))
            |> BatEnum.filter_map (fun entry ->
                let tuple = List.map Smt.int_val (FuncEntry.get_args entry) in
                if Smt.bool_val (FuncEntry.get_value entry) then
                  Some (p, tuple)
                else
                  None)
            |> Config.make
          end)
  |> BatEnum.reduce Config.union
  
let entailment_cex ctx predicates phi psi =
  let solver = new Smt.solver ctx in
  let open BatPervasives in
  let open F in
  solver#add phi;
  solver#add_not psi;
  match Smt.get_min_model solver with
  | `Sat (m, size) ->
    let solver = new Smt.solver ctx in
    let universe = BatList.of_enum (1 -- size) in

    solver#add (instantiate_quantifiers phi universe);
    solver#add_not (instantiate_quantifiers psi universe);
    let m =
      match solver#get_model () with
      | `Sat m -> m
      | `Unsat | `Unknown -> assert false
    in
    Some (model_of_z3 m predicates size)
  | `Unsat -> None
  | `Unknown -> failwith "entailment_cex: unknown"

let check_emptiness_certificate pa phi =
  let gensym =
    let n = ref 0 in
    fun x ->
      incr n;
      F.alpha_of_int (!n)
  in
  let string_of_rel = Memo.memo (fun _ -> gensym ()) in
  let pp_rel formatter rel =
    Format.pp_print_string formatter (string_of_rel rel)
  in
  let pp phi =
    F.tptp3_pp pp_rel Format.pp_print_int phi
  in
  Alphabet.Set.iter (fun alpha ->
      let file = Filename.temp_file "inv-check" ".p" in
      let chan = open_out file in
      let fmt = Format.formatter_of_out_channel chan in
      
      let post = A.post pa phi alpha in

      Format.fprintf fmt "fof(cert,axiom,%a)." pp phi;
      Format.fprintf fmt "fof(post_cert,conjecture,%a)." pp post;
      close_out chan;
      Format.printf "Checking post %s (%s)@." alpha file;
      eprover file
    ) (A.alphabet pa)

let check_emptiness_certificate pa phi =
  let ctx = new Smt.ctx [("model", "true")] in
  BatEnum.iter (fun (p, arity) -> ctx#register_rel p arity) (A.vocabulary pa);
  Alphabet.Set.iter (fun alpha ->
      let post = A.post pa phi alpha in
      match entailment_cex ctx (A.vocabulary pa) post phi with
      | Some m ->
        logf "Found counter-example for consecution:";
        let rec find_pred i =
          if i > Config.universe_size m then begin
            Log.errorf "Could not find predecessor";
            Log.errorf "Letter: %s" alpha;
            Log.errorf "Simplified post:@\n%a"
              pp_formula
              (match Config.instantiate m post with
               | Some x -> x
               | None -> assert false);
            failwith "No predecessor"
          end;
          let p = A.pred pa m (alpha, i) in
          if Config.models p phi then (Config.minimize p phi, i)
          else find_pred (i + 1)
        in
        let (predecessor, i) = find_pred 1 in
        logf "  @[%a@]" Config.pp predecessor;
        logf "    --( %s : %d )-> " alpha i;
        logf "  @[%a@]" Config.pp m;
        logf "Simplified pre:@\n @[%a@]"
          pp_formula
          (BatOption.get (Config.instantiate predecessor phi));
        logf "Simplified post:@\n @[%a@]"
          pp_formula
          (BatOption.get (Config.instantiate m post))
      | None ->
        logf "Invariant is inductive w.r.t. %s" alpha
    ) (A.alphabet pa)
  
let check_invariant pa phi =
  logf "Checking invariant:@\n%a" pp_formula phi;
  Bounded.bounded_invariant pa 2 phi

let run pa word =
  let ctx = new Smt.ctx [("model", "true")] in
  BatEnum.iter (fun (p, arity) -> ctx#register_rel p arity) (A.vocabulary pa);

  let universe =
    List.fold_left (fun m (_, k) -> max m k) 1 word
  in
  let start =
    let open BatPervasives in
    F.instantiate_quantifiers
      (A.initial pa)
      (BatList.of_enum (1 -- universe))
  in
  logf "%a" pp_formula start;
  let final =
    List.fold_right
      (fun (alpha, i) phi ->
         let psi =
           A.concrete_post pa phi (alpha, i) |> Smt.simplify_dillig ctx
         in
         logf "  <%s : %i>" alpha i;
         logf "%a" pp_formula psi;
         psi
      )
      word
      start
  in
  if A.accepting_formula pa final then
    logf "<- Accepting";
  final

let check_embeddings embeds structs reName =
  (* Renames arguments to be from 1 to n *)
  let rename str =
    let inv = BatDynArray.create() in (* Inverse Mapping *)
    BatDynArray.add inv 0;            (* Psuedo 1-indexing *)
    let f (str, map) (head, args) =
      let g (args, map) arg =
        if (Putil.PInt.Map.mem arg map) then
          ((Putil.PInt.Map.find arg map) :: args), map
        else
          begin
            BatDynArray.add inv arg;
            ((BatDynArray.length inv) :: args), (Putil.PInt.Map.add arg (BatDynArray.length inv) map)
          end
      in
      let (args, m) = List.fold_left g ([], map) args in
      (Config.add head args str), m
    in
    let (str, map) = (BatEnum.fold f ((Config.empty 1), Putil.PInt.Map.empty) (Config.props str)) in
    str, inv
  in
  let rec go structs =
    match structs with
    | [] -> ()
    | (c, c') :: structs' ->
       (if reName then
         begin
           let str, inv = rename c in
           let str', inv' = rename c' in
           print_endline (if embeds str str' then "True" else "False")
         end
       else
         print_endline (if embeds c c' then "True" else "False"));
       go structs'
  in go structs  

let _ =
  Log.verbosity_level := `info;
  match Sys.argv.(1) with
  | "run" ->
    let pa = load_automaton Sys.argv.(2) in
    let word = load_word Sys.argv.(3) in
    ignore (run pa word)
  | "echo" ->
    let pa = load_automaton Sys.argv.(2) in
    A.pp Format.std_formatter pa
  | "negate" ->
    let pa = load_automaton Sys.argv.(2) in
    A.pp Format.std_formatter (A.negate pa)
  | "diff" ->
    let program = load_automaton Sys.argv.(2) in
    let proof = load_automaton Sys.argv.(3) in
    A.pp Format.std_formatter (A.intersect program (A.negate proof))
  | "ground" ->
    let pa = load_automaton Sys.argv.(2) in
    let size = int_of_string Sys.argv.(3) in
    A.pp_ground size Format.std_formatter pa
  | "empty" ->
    let pa = load_automaton Sys.argv.(2) in
    begin match Empty.find_word (Empty.mk_solver pa) with
      | None ->
        logf ~level:`always
          "The input predicate automaton accepts an empty language"
      | Some _ -> ()
    end
  | "bounded-empty" ->
    let pa = load_automaton Sys.argv.(2) in
    let size = int_of_string Sys.argv.(3) in
    begin match bounded_empty pa size with
      | None ->
        logf ~level:`always
          "The input predicate automaton accepts no words with over an \
           alphabet with %d thread(s)"
          size
      | Some _ -> ()
    end
  | "embeds" ->
     if Array.length Sys.argv > 3 then
       check_embeddings Config.embeds_novel2 (load_structs Sys.argv.(3)) (match Sys.argv.(2) with | "rename" -> true | _ -> false)
     else
       check_embeddings Config.embeds_novel2 (load_structs Sys.argv.(2)) false
  | "uembeds" ->
     if Array.length Sys.argv > 3 then
       check_embeddings Config.uembeds (load_structs Sys.argv.(3)) (match Sys.argv.(2) with | "rename" -> true | _ -> false)
     else
       check_embeddings Config.uembeds (load_structs Sys.argv.(2)) false
  | "diff-check" ->
    let program = load_automaton Sys.argv.(2) in
    let proof = load_automaton Sys.argv.(3) in
    let phi  = load_formula Sys.argv.(4) in
    let diff = intersect program (complement proof) in
    check_emptiness_certificate diff phi
  | "diff-inv" ->
    let program = load_automaton Sys.argv.(2) in
    let proof = load_automaton Sys.argv.(3) in
    let phi  = load_formula Sys.argv.(4) in
    let diff = intersect program (complement proof) in
    ignore (check_invariant diff phi)
  | "diff-empty" ->
    let program = load_automaton Sys.argv.(2) in
    let proof = load_automaton Sys.argv.(3) in
    let diff = intersect program (complement proof) in
    ignore (bounded_empty diff 2)
  | x -> Log.fatalf "Unknown command: `%s'" x
