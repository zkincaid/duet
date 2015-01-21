open Apak
open OUnit
open ArkPervasives
open BatPervasives


let nudge1 () =
  let q =
    QQ.of_string "3738586354233779120801461861777915892452276847625450180710355696989/210624583337114373395836055367340864637790190801098222508621955072"
  in
  let q_lo = QQ.nudge_down q in
  let q_hi = QQ.nudge_up q in
  assert_bool "nudge_down(q) <= q" (QQ.leq q_lo q);
  assert_bool "q <= nudge_up(q)" (QQ.leq q q_hi)


let nudge2 () =
  let q =
    QQ.of_string "-4301235912375093281437218183421982719847231350958423194328193248321/112341239847548932174321894327189432748383888881237489123651201011"
  in
  let q_lo = QQ.nudge_down q in
  let q_hi = QQ.nudge_up q in
  assert_bool "nudge_down(q) <= q" (QQ.leq q_lo q);
  assert_bool "q <= nudge_up(q)" (QQ.leq q q_hi)


let nudge3 () =
  let q =
    QQ.of_string "3738586354233779120801461861777915892452276847625450180710355696989/210624583337114373395836055367340864637790190801098222508621955072"
  in
  let q_lo = QQ.nudge_down ~accuracy:100 q in
  let q_hi = QQ.nudge_up ~accuracy:100 q in
  assert_bool "nudge_down(q) = q" (QQ.equal q_lo q);
  assert_bool "q = nudge_up(q)" (QQ.equal q q_hi)

let suite = "Pervasives" >:::
  [
    "nudge1" >:: nudge1;
    "nudge2" >:: nudge2;
    "nudge3" >:: nudge3;
  ]
