#!/bin/bash
ocamlbuild solve.cmx -package ocamlgraph -package gmp
ocamlbuild solve.native -package ocamlgraph -package gmp
