(*pp deriving *)
(* Test build with
   ocamlc -o dtest -I $DERIVING_HOME/lib -pp $DERIVING_HOME/syntax/deriving deriving.cma DerivingTest.ml
*)

type foo = int list deriving (Show)

let _ =
   let three = 3 in
      if three < 7 then
        ()
      else
         assert false
