#!/bin/bash

#ocamlc -pp "camlp4o pa_extend.cmo" -I +camlp4 -c assumeassertparser.ml
#ocamlfind ocamlc -package camlp4 -package camlp4.gramlib -linkpkg assumeassertparser.cmo -o parser.byte # works

ocamlopt -pp "camlp4o pa_extend.cmo" -I +camlp4 -c assumeassertparser.ml || exit 1
ocamlfind ocamlopt -package camlp4 -package camlp4.gramlib -linkpkg assumeassertparser.cmx -o parser.native
