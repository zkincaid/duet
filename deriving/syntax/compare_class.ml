(*pp camlp4of *)

(* Copyright Jeremy Yallop 2007.
   This file is free software, distributed under the MIT license.
   See the file COPYING for details.
*)
module InContext (L : Base.Loc) =
struct
  open Base
  open Utils
  open Type
  open Camlp4.PreCast
  include Base.InContext(L)
  
  let classname = "Compare"

  let lprefix = "l" and rprefix = "r"

  (* last two cases can never be matched *)
  let rec drop_unused = function
    | [] -> assert false
    | [x;y] -> []
    | (x::xs) -> x::(drop_unused xs)

  let make_cases f xs = drop_unused (List.concat (List.map f xs))

  let tup ctxt ts mexpr exp = 
      match ts with
        | [t] -> 
            <:module_expr< struct type a = $atype_expr ctxt (`Tuple ts)$;
                                  value compare l r = let module M = $exp ctxt t$ 
                                   in $mexpr$ l r; end >>

        | ts ->
            let _, (lpatt, rpatt), expr = 
              List.fold_right
                (fun t (n, (lpatt, rpatt), expr) ->
                   let lid = Printf.sprintf "l%d" n and rid = Printf.sprintf "r%d" n in
                     (n+1,
                      (Ast.PaCom (loc,<:patt< $lid:lid$ >>, lpatt),
                       Ast.PaCom (loc,<:patt< $lid:rid$ >>, rpatt)),
                      <:expr< let module M = $exp ctxt t$ 
                              in 
               		      let cmp = $mexpr$ $lid:lid$ $lid:rid$ in
                                if cmp = 0 then $expr$ else cmp >>))
                ts
                (0, (<:patt< >>, <:patt< >>), <:expr< 0 >>)
            in 
              <:module_expr< struct type a = $atype_expr ctxt (`Tuple ts)$;
                                    value compare $Ast.PaTup (loc, lpatt)$ $Ast.PaTup (loc, rpatt)$ = $expr$; end >>
    
  let instance = object (self)
    inherit make_module_expr ~classname ~allow_private:true

    method tuple ctxt ts = tup ctxt ts <:expr< M.compare >> (self#expr)

    method case ctxt : Type.summand -> Ast.match_case list = 
      fun (name,args) ->
	match args with 
          | [] ->
	      [ <:match_case< ($uid:name$, $uid:name$) -> 0 >>;
		<:match_case< ($uid:name$, _) -> 1 >>;
		<:match_case< (_, $uid:name$) -> -1 >> ]
          | _ -> 
              let nargs = List.length args in
              let lpatt, lexpr = tuple ~param:"l" nargs
              and rpatt, rexpr = tuple ~param:"r" nargs in
		[ <:match_case<
                    ($uid:name$ $lpatt$, $uid:name$ $rpatt$) ->
		  $mproject (self#expr ctxt (`Tuple args)) "compare"$ $lexpr$ $rexpr$ >>;
		  <:match_case< ($uid:name$ _, _) -> 1 >>;
		  <:match_case< (_, $uid:name$ _) -> -1 >> ]

    method sum ?eq ctxt decl summands = 
      let cases = make_cases (self#case ctxt) summands in
	<:module_expr< 
          struct
            type a = $atype ctxt decl$;
            value compare l r = match (l, r) with 
              [ $list:cases$ ];
          end >>


  method field ctxt : Type.field -> Ast.expr = function
    | (name, ([], t), `Immutable)
    | (name, ([], t), `Mutable) ->
        <:expr<
          $mproject (self#expr ctxt t) "compare"$ $lid:lprefix ^ name$ $lid:rprefix ^ name$ >>
    | f -> raise (Underivable ("Compare cannot be derived for record types with polymorphic fields")) 


  method record ?eq ctxt decl fields =
    let lpatt = record_pattern ~prefix:"l" fields
    and rpatt = record_pattern ~prefix:"r" fields 
    and expr = 
      List.fold_right
        (fun f e -> <:expr<
           let cmp = $self#field ctxt f$ in
             if cmp != 0 then cmp else $e$ >>)
        fields
        <:expr< 0 >>
    in <:module_expr< struct type a = $atype ctxt decl$;
                             value compare $lpatt$ $rpatt$ = $expr$; end >>

    method polycase ctxt : Type.tagspec -> Ast.match_case list = function
      | Tag (name, None) ->
	  [ <:match_case< (`$name$, `$name$) -> 0 >>;
            <:match_case< (`$name$, _) -> 1 >>;
            <:match_case< (_, `$name$) -> -1 >> ]
      | Tag (name, Some e) ->
	  [ <:match_case< (`$name$ l, `$name$ r) -> 
              $mproject (self#expr ctxt e) "compare"$ l r >>;
            <:match_case< (`$name$ _, _) -> 1 >>;
	    <:match_case< (_, `$name$ _) -> -1 >>]
      | Extends t -> 
          let lpatt, lguard, lcast = cast_pattern ctxt ~param:"l" t in
          let rpatt, rguard, rcast = cast_pattern ctxt ~param:"r" t in
            [ <:match_case<
               ($lpatt$, $rpatt$) when $lguard$ && $rguard$ ->
                 $mproject (self#expr ctxt t) "compare"$ $lcast$ $rcast$ >>;
              <:match_case< ($lpatt$, _) when $lguard$ -> 1 >>;
              <:match_case< (_, $rpatt$) when $rguard$ -> -1 >> ]

    method variant ctxt decl (spec, tags) = 
      <:module_expr< struct type a = $atype ctxt decl$;
                            value compare l r = match (l, r) with
                                [ $list:make_cases (self#polycase ctxt) tags$ ];
                     end >>
  end
end

let _ = Base.register "Compare" 
  ((fun (loc, context, decls) -> 
      let module M = InContext(struct let loc = loc end) in   
        M.generate ~context ~decls ~make_module_expr:M.instance#rhs ~classname:M.classname
          ~default_module:"Defaults" ()),
   (fun (loc, context, decls) ->
      let module M = InContext(struct let loc = loc end) in
        M.gen_sigs ~classname:M.classname ~context ~decls))
