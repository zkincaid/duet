#!/bin/bash
ocamlbuild solve.cmx -package ocamlgraph
ocamlbuild solve.native -package ocamlgraph
