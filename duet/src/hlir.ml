(** Translations of high level language constructs into low level IR *)

open Core
open Ast
let stmt_of_def file def = mk_stmt file (Instr [Def.mk def])

let trivial_cond =
  let f = function
    | OHavoc _ -> true
    | OConstant _ -> false
    | OCast (_, t) -> t
    | OBinaryOp (a, _, b, _) -> a || b
    | OUnaryOp (_, t, _) -> t
    | OAccessPath _ -> false
    | OBoolExpr t -> t
    | OAddrOf _ -> false
  in
  let g = function
    | OAtom (_, a, b) -> a || b
    | OOr (a, b) -> a || b
    | OAnd (a, b) -> a && b
  in
  Bexpr.deep_fold f g

let mk_if file cond (bthen : stmt list) (belse : stmt list) =
  if trivial_cond cond
  then mk_stmt file (Branch (mk_stmt file (Block bthen),
                             mk_stmt file (Block belse)))
  else begin
    let mk_branch cond code =
      mk_stmt file (Block ((stmt_of_def file (Assume cond))::code))
    in
    let bthen = mk_branch cond bthen in
    let belse = mk_branch (Bexpr.negate cond) belse in
    mk_stmt file (Branch (bthen, belse))
  end

let mk_skip file = stmt_of_def file (Assume Bexpr.ktrue)

let mk_while file cond body =
  let loop_start = mk_skip file in
  let loop_end = mk_skip file in
  mk_stmt file
    (Block [loop_start;
            mk_if file cond (body@[mk_stmt file (Goto (stmt_id loop_start))])
              [mk_stmt file (Goto (stmt_id loop_end))];
            loop_end])
