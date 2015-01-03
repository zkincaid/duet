open Core
open Apak
open CfgIr
open BatPervasives

let star_count = ref 0
let mul_count = ref 0
let add_count = ref 0

module K = struct
  include Putil.PInt
  type var = Core.var
  let star _ = (incr star_count; 1)
  let mul x y = (incr mul_count; x * y)
  let add x y = (incr add_count; x + y)
  let widen _ _  = 1
  let zero = 0
  let one = 1
  let exists _ k = k
end

module Initial = struct
  type t =
  | Add of t * t
  | Mul of t * t
  | Star of t
  | Atom of Def.t
  | One
  | Zero
  | Top
      deriving (Show, Compare)
  let format = Show_t.format
  let show = Show_t.show
  let compare = Compare_t.compare
  let equal x y = compare x y = 0
  type var = Core.var
  let star x = Star x
  let mul x y = Mul (x, y)
  let add x y = Add (x, y)
  let widen _ _  = Top
  let zero = Zero
  let one = One
  let exists _ k = k
end


module A = Interproc.MakePathExpr(K)
module AI = Interproc.MakePathExpr(Initial)

let analyze file =
  match file.entry_points with
  | [main] -> begin
    let rg = Interproc.make_recgraph file in
    let local func_name _ = false in
    let weight _ = 1 in
    let query = A.mk_query rg weight local main in
    let is_assert def = match def.dkind with
      | Assert (_, _) | AssertMemSafe _ -> true
      | _             -> false
    in
    let check_assert def path =
      Log.logf ~level:0 "%d paths to %a" path Def.format def
    in
    A.compute_summaries query;
    let summary_mul = !mul_count in
    let summary_add = !add_count in
    let summary_star = !star_count in
    Log.logf ~level:0 "Path operations for summarization:";
    Log.logf ~level:0 "  Multiplication: %d" summary_mul;
    Log.logf ~level:0 "  Addition:       %d" summary_add;
    Log.logf ~level:0 "  Star:           %d" summary_star;
    BatEnum.iter (fun block ->
      Log.logf ~level:0 "Paths in `%a': %d"
	Varinfo.format block
	(A.get_summary query block)
    ) (Interproc.RG.blocks rg);

    ignore (A.single_src_blocks query main);
    let interproc_mul = !mul_count - summary_mul in
    let interproc_add = !add_count - summary_add in
    let interproc_star = !star_count - summary_star in
    Log.logf ~level:0 "Path operations for interprocedural paths:";
    Log.logf ~level:0 "  Multiplication: %d" interproc_mul;
    Log.logf ~level:0 "  Addition:       %d" interproc_add;
    Log.logf ~level:0 "  Star:           %d" interproc_star;

    A.single_src_restrict query is_assert check_assert;
    Log.logf ~level:0 "Total path operations:";
    Log.logf ~level:0 "  Multiplication: %d" (!mul_count);
    Log.logf ~level:0 "  Addition:       %d" (!add_count);
    Log.logf ~level:0 "  Star:           %d" (!star_count);

  end
  | _ -> assert false


let analyze_pathexp file =
  match file.entry_points with
  | [main] -> begin
    let rg = Interproc.make_recgraph file in
    let local func_name _ = false in
    let weight def = Initial.Atom def in
    let query = AI.mk_query rg weight local main in
(*
    BatEnum.iter (fun block ->
      Log.logf 0 "Graph for block `%a'"
	Varinfo.format block;
      Interproc.RGD.display (Interproc.RG.block_body rg block)
    ) (Interproc.RG.blocks rg);
*)

    AI.compute_summaries query;
    BatEnum.iter (fun block ->
      Log.logf ~level:0 "Path expression for `%a':@\n%a"
	Varinfo.format block
	Initial.format (AI.get_summary query block)
    ) (Interproc.RG.blocks rg);
  end
  | _ -> assert false

let _ =
  CmdLine.register_pass
    ("-pathexp", analyze_pathexp, " Compute path expressions")
let _ =
  CmdLine.register_pass
    ("-pathstats", analyze, " Compute path expression statistics")
