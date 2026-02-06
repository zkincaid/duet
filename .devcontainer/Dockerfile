FROM ubuntu:24.04

ENV DEBIAN_FRONTEND=noninteractive 
ARG USERNAME=duet

## BEGIN: RUNS AS ROOT

RUN apt-get update -y
RUN apt-get install -y build-essential
RUN apt-get install -y m4
RUN apt-get install -y curl
RUN apt-get install -y jq
RUN apt-get install -y opam
RUN apt-get install -y zip
RUN apt-get install -y libgmp-dev
RUN apt-get install -y libmpfr-dev
RUN apt-get install -y python3
RUN apt-get install -y python-is-python3
RUN apt-get install -y libffi-dev
RUN apt-get install -y pkg-config
RUN apt-get install -y autoconf
RUN apt-get install -y libtool
RUN apt-get install -y libflint-dev
RUN apt-get install -y default-jre

## Run in usermode

# [Optional] Set the default user. Omit if you want to keep the default as root.
USER $USERNAME

# Configure opam/ocaml
RUN opam init -y --disable-sandboxing --compiler=5.4.0
RUN opam switch 5.4.0
RUN opam remote add sv https://github.com/zkincaid/sv-opam.git
RUN opam install -y dune
RUN opam install -y num
RUN opam install -y menhir
RUN opam install -y utop
RUN opam install -y ocamlformat
RUN opam install -y ocaml-lsp-server
RUN opam install -y zarith
RUN opam install -y ocamlgraph
RUN opam install -y batteries
RUN opam install -y ppx_deriving
RUN opam install -y ounit
RUN opam install -y ctypes-foreign
RUN opam install -y cil
RUN opam install -y apron
RUN opam install -y normalizffi
RUN opam install -y flint.dev
RUN opam install -y faugere.dev
RUN opam install -y z3

RUN eval `opam config env`
