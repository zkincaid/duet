module Ctx = Srk.Syntax.MakeContext ()
let srk = Ctx.context
let solver = Srk.SrkZ3.Solver.make srk
let max_malloc = ref (-1)