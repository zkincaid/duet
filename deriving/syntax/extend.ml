(*pp camlp4orf *)

(* Copyright Jeremy Yallop 2007.
   This file is free software, distributed under the MIT license.
   See the file COPYING for details.
*)

(* Extend the OCaml grammar to include the `deriving' clause after
   type declarations in structure and signatures. *)

open Utils

module Deriving (Syntax : Camlp4.Sig.Camlp4Syntax) =
struct
  open Camlp4.PreCast

  include Syntax

  let fatal_error loc msg = 
    Syntax.print_warning loc msg;
    exit 1

  let display_errors loc f p =
    try
      f p
    with 
        Base.Underivable msg | Failure msg ->
          fatal_error loc msg

  let derive proj (loc : Loc.t) tdecls classname =
    let context = display_errors loc (Base.setup_context loc) tdecls in
      display_errors loc
        (proj (Base.find classname)) (loc, context, tdecls)

  let derive_str loc (tdecls : Type.decl list) classname : Ast.str_item =
    derive fst loc tdecls classname

  let derive_sig loc tdecls classname : Ast.sig_item =
    derive snd loc tdecls classname


  DELETE_RULE Gram str_item: "type"; type_declaration END
  DELETE_RULE Gram sig_item: "type"; type_declaration END

  open Ast

  EXTEND Gram
  str_item:
  [[ "type"; types = type_declaration -> <:str_item< type $types$ >>
    | "type"; types = type_declaration; "deriving"; "("; cl = LIST0 [x = UIDENT -> x] SEP ","; ")" ->
        let decls = display_errors loc Type.Translate.decls types in 
        let module U = Type.Untranslate(struct let loc = loc end) in
        let tdecls = List.map U.decl decls in
          <:str_item< type $list:tdecls$; $list:List.map (derive_str loc decls) cl$ >>
   ]]
  ;
  sig_item:
  [[ "type"; types = type_declaration -> <:sig_item< type $types$ >>
   | "type"; types = type_declaration; "deriving"; "("; cl = LIST0 [x = UIDENT -> x] SEP "," ; ")" ->
       let decls  = display_errors loc Type.Translate.decls types in 
       let module U = Type.Untranslate(struct let loc = loc end) in
       let tdecls = List.concat_map U.sigdecl decls in
       let ms = List.map (derive_sig loc decls) cl in
         <:sig_item< type $list:tdecls$; $list:ms$ >> ]]
  ;
  END

(*
  let pr = print_endline
  let pr2 x y = pr (x ^ " " ^ y)
*)
  let mk_anti ?(c = "") n s = "\\$"^n^c^":"^s

  let derive_ast loc classname methodname t =
(*
  EXTEND Gram
  expr: LEVEL "simple"
  [
  [e1 = TRY val_longident ; "<" ; t = ctyp; ">" ->
     match e1 with
       | <:ident< $uid:classname$ . $lid:methodname$ >> ->
*)
         if not (Base.is_registered classname) then
           fatal_error loc ("deriving: "^ classname ^" is not a known `class'")
         else
           let module U = Type.Untranslate(struct let loc = loc end) in
           let binding = Ast.TyDcl (loc, "inline", [], t, []) in
           let decls = display_errors loc Type.Translate.decls binding in
             if List.exists Base.contains_tvars_decl decls then
               fatal_error loc ("deriving: type variables cannot be used in `method' instantiations")
             else
               let tdecls = List.map U.decl decls in
               let m = derive_str loc decls classname in
                 <:expr< let module $uid:classname$ = 
                             struct
                               type $list:tdecls$;
                               $m$;
                               include $uid:classname ^ "_inline"$;
                             end
                          in $uid:classname$.$lid:methodname$ >>

  try
  DELETE_RULE Gram expr: val_longident END;
  with Not_found -> () (* ocaml >= 3.12.0 *)
;; 

  EXTEND Gram
  GLOBAL: expr;
  expr: LEVEL "simple"
  [[
   a = ident2 -> match a with
                 | `Ident i -> <:expr< $id:i$ >>
                 | `Deriving (c,m,t) -> derive_ast loc c m t
  ]];
  ident2:
    [ [ `ANTIQUOT ((""|"id"|"anti"|"list" as n),s) ->
          `Ident <:ident< $anti:mk_anti ~c:"ident" n s$ >>
      | i = a_UIDENT -> (*pr2 "UID" i;*) `Ident <:ident< $uid:i$ >>
      | i = a_LIDENT -> (*pr2 "LID" i;*) `Ident <:ident< $lid:i$ >>
      | i = a_UIDENT; "."; j = a_LIDENT; "<"; t = ctyp; ">" -> (*pr "RULE";*) `Deriving (i,j,t)
      | i = a_UIDENT; "."; j = a_LIDENT -> `Ident <:ident< $uid:i$.$lid:j$ >>
      | `ANTIQUOT ((""|"id"|"anti"|"list" as n),s); "."; i = ident ->
          `Ident <:ident< $anti:mk_anti ~c:"ident" n s$.$i$ >>
      | i = a_UIDENT; "."; j = ident -> (*pr2 "COMPOSE" i;*) `Ident <:ident< $uid:i$.$j$ >> ] ]
  ;
  END

end

module M = Camlp4.Register.OCamlSyntaxExtension(Id)(Deriving)

