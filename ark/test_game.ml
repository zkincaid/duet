open OUnit
open Quantifier
open Syntax
open Apak

module Ctx = MakeSimplifyingContext ()
module Infix = Syntax.Infix(Ctx)
let ctx = Ctx.context
let smt_ctx = ArkZ3.mk_context ctx []

let wsym = Ctx.mk_symbol ~name:"w" `TyReal
let xsym = Ctx.mk_symbol ~name:"x" `TyReal
let ysym = Ctx.mk_symbol ~name:"y" `TyReal
let zsym = Ctx.mk_symbol ~name:"z" `TyReal

let w = mk_const ctx wsym
let x = mk_const ctx xsym
let y = mk_const ctx ysym
let z = mk_const ctx zsym

let int k = Ctx.mk_real (QQ.of_int k)
let frac i j = Ctx.mk_real (QQ.of_frac i j)

let reach1 () =
  let start =
    let open Infix in
    x = (int 0)
  in
  let safe =
    let open Infix in
    x < (int 5) && y = x
  in
  let reach =
    let open Infix in
    x = y + (int 1)
  in
  assert_equal None (Game.solve ctx ([xsym],[ysym]) ~start ~safe ~reach)

let safe1 () =
  let start =
    let open Infix in
    x = (int 0)
  in
  let reach =
    let open Infix in
    x < (int 3) && y = x
  in
  let safe =
    let open Infix in
    x < (int 3) && y = x + (int 1)
  in
  assert_bool
    "No winning strategy for safety player"
    ((Game.solve ctx ([xsym],[ysym]) ~start ~safe ~reach) != None)

let b1 = Ctx.mk_symbol ~name:"b1" `TyReal
let b2 = Ctx.mk_symbol ~name:"b2" `TyReal
let b3 = Ctx.mk_symbol ~name:"b3" `TyReal
let b4 = Ctx.mk_symbol ~name:"b4" `TyReal
let b5 = Ctx.mk_symbol ~name:"b5" `TyReal
let b1' = Ctx.mk_symbol ~name:"b1'" `TyReal
let b2' = Ctx.mk_symbol ~name:"b2'" `TyReal
let b3' = Ctx.mk_symbol ~name:"b3'" `TyReal
let b4' = Ctx.mk_symbol ~name:"b4'" `TyReal
let b5' = Ctx.mk_symbol ~name:"b5'" `TyReal

let buckets = [b1; b2; b3; b4; b5]
let buckets' = [b1'; b2'; b3'; b4'; b5']

let bucket_init =
  let nonneg =
    List.map (fun b -> Ctx.mk_leq (int 0) (Ctx.mk_const b)) buckets
  in
  let total_one =
    Ctx.mk_eq (Ctx.mk_add (List.map Ctx.mk_const buckets)) (int 1)
  in
  Ctx.mk_and (total_one::nonneg)

let stepmother = (* going from buckets' -> buckets *)
  let filled = Ctx.mk_add (List.map Ctx.mk_const buckets) in
  let filled' = Ctx.mk_add (List.map Ctx.mk_const buckets') in
  let increasing =
    List.map2
      (fun b b' -> Ctx.mk_leq (Ctx.mk_const b') (Ctx.mk_const b))
      buckets
      buckets'
  in
  Ctx.mk_and ((Ctx.mk_eq filled (Ctx.mk_add [filled'; (int 1)]))::increasing)

let cinderella capacity = (* going from buckets -> buckets' *)
  let not_spilled =
    buckets |> List.map (fun b ->
        Ctx.mk_leq (Ctx.mk_const b) capacity)
    |> Ctx.mk_and
  in
  let empty (b1,b1') (b2,b2') (b3,b3') (b4,b4') (b5,b5') =
    Ctx.mk_and [Ctx.mk_eq b1' (int 0);
                Ctx.mk_eq b2' (int 0);
                Ctx.mk_eq b3' b3;
                Ctx.mk_eq b4' b4;
                Ctx.mk_eq b5' b5]
  in
  let bucket1 = (Ctx.mk_const b1, Ctx.mk_const b1') in
  let bucket2 = (Ctx.mk_const b2, Ctx.mk_const b2') in
  let bucket3 = (Ctx.mk_const b3, Ctx.mk_const b3') in
  let bucket4 = (Ctx.mk_const b4, Ctx.mk_const b4') in
  let bucket5 = (Ctx.mk_const b5, Ctx.mk_const b5') in
  let choose_empty =
    Ctx.mk_or [empty bucket1 bucket2 bucket3 bucket4 bucket5;
               empty bucket2 bucket3 bucket4 bucket5 bucket1;
               empty bucket3 bucket4 bucket5 bucket1 bucket2;
               empty bucket4 bucket5 bucket1 bucket2 bucket3;
               empty bucket5 bucket1 bucket2 bucket3 bucket4]
  in
  Ctx.mk_and [not_spilled; choose_empty]

let cinderella1 () =
  assert_bool
    "No winning strategy for safety player"
    ((Game.solve
        ctx
        (buckets,buckets')
        ~start:bucket_init
        ~safe:(cinderella (frac 30 10))
        ~reach:stepmother) != None)

let suite = "Game" >::: [
    "reach1" >:: reach1;
    "safe1" >:: safe1;
    "cinderella1" >:: cinderella1;
  ]
