#!/bin/bash
ocamlbuild mprs.cmx -package ocamlgraph -package gmp
ocamlbuild run_tests.native -package ocamlgraph -package gmp
