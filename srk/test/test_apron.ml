open OUnit
open Syntax
open SrkApron
open Test_pervasives

let env = Env.of_list srk [xsym; ysym; zsym]

let roundtrip1 () =
  let t =
    let open Infix in
    (x + y) / (int 5) + ((int 2) * x)
  in
  let t2 = term_of_texpr env (texpr_of_term env t) in
  assert_equal ~cmp:Term.equal ~printer:(Term.show srk) t t2

let roundtrip2 () =
  let t =
    let open Infix in
    Ctx.mk_floor ((x + y) / (((int 2) / (int 5)) + z)) + (int 1)
  in
  let t2 = term_of_texpr env (texpr_of_term env t) in
  assert_equal ~cmp:Term.equal ~printer:(Term.show srk) t t2

let roundtrip3 () = 
  let t =
    let open Infix in
    Ctx.mk_mod (x + (int 5)) (int 2)
  in
  let t2 = term_of_texpr env (texpr_of_term env t) in
  assert_equal ~cmp:Term.equal ~printer:(Term.show srk) t t2

module Vec = Linear.QQVector
let roundtrip4 () =
  let t =
    let open Infix in
    Linear.linterm_of srk ((x - y) + ((int 3) * x))
  in
  let t2 = vec_of_lexpr env (lexpr_of_vec env t) in
  assert_equal ~cmp:Vec.equal ~printer:Vec.show t t2

let roundtrip5 () =
  let t =
    let open Infix in
    Linear.linterm_of srk (((x + y) / ((int 2) / (int 5))) + (int 1))
  in
  let t2 = vec_of_lexpr env (lexpr_of_vec env t) in
  assert_equal ~cmp:Vec.equal ~printer:Vec.show t t2

let of_constraints env man constraints =
  let f = function
    | `Leq (s, t) -> tcons_geqz (texpr_of_term env (Ctx.mk_sub t s))
    | `Eq (s, t) -> tcons_eqz (texpr_of_term env (Ctx.mk_sub t s))
    | `Lt (s, t) -> tcons_gtz (texpr_of_term env (Ctx.mk_sub t s))
  in
  meet_tcons (top man env) (List.map f constraints)

let env1 () =
  let env1 = Env.of_list srk [xsym; ysym] in
  let env2 = Env.of_list srk [ysym; zsym] in
  let env3 = Env.of_list srk [xsym; ysym; zsym] in
  let man = Polka.manager_alloc_strict () in
  let prop1 = of_constraints env1 man [`Leq (x, y)] in
  let prop2 = of_constraints env2 man [`Lt (y, z)] in
  let prop3 = of_constraints env3 man [`Leq (x, y); `Lt (y, z)] in
  let prop4 = meet prop1 prop2 in
  assert_equal ~cmp:equal ~printer:show prop3 prop4

let env2 () =
  let env1 = Env.of_list srk [wsym; xsym; zsym] in
  let env2 = Env.of_list srk [xsym; ysym; zsym] in
  let env3 = Env.of_list srk [wsym; xsym; ysym; zsym] in
  let man = Polka.manager_alloc_loose () in
  let prop1 = of_constraints env1 man [`Leq (x, w); `Leq (w, z)] in
  let prop2 = of_constraints env2 man [`Leq (x, z); `Leq (y, z)] in
  let prop3 = of_constraints env3 man [`Leq (x, z)] in
  let prop4 = join prop1 prop2 in
  assert_equal ~cmp:equal ~printer:show prop3 prop4

let suite = "SrkApron" >::: [
    "roundtrip1" >:: roundtrip1;
    "roundtrip2" >:: roundtrip2;
    "roundtrip3" >:: roundtrip3;
    "roundtrip4" >:: roundtrip4;
    "roundtrip5" >:: roundtrip5;
    "env1" >:: env1;
    "env2" >:: env2;
  ]
