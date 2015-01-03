open Libduet
open Core

module type Interpretation = sig
  include Domain
  val transfer : def -> t -> t
  val assert_true : std_bexpr -> t -> bool
  val assert_memsafe : std_expr -> t -> bool
  val name : string
end

struct Make (I : Interpretation) = struct
  let simplify_func map func =
    let changed := ref false in
    let simplify_expr expr = expr in
    let simplify_def def =
      match v.dkind with
      | Assume phi ->
	let phi = simplify_bexpr phi in
	
      | Assert (psi, _) -> ()
      | Assignment (lhs, rhs)
      | _ -> ()
    in
    Cfg.iter_vertex simplify_def func.cfg;
    CfgIr.remove_unreachable func.cfg init;
    !changed

  let simplify_file map file =
    let changed := ref false in
    let simplify_func func =
      let func_changed = simplify_func map func in
      changed := !changed || func_changed
    in
    List.iter (process_func map) file.funcs;
    !changed
end
