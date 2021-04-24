#!/bin/bash
# This script will install dependencies then build ComPACT

if [ $(id -u) != "0" ]; then
echo "You must be the superuser to run this script" >&2
exit 1
fi
apt-get update

echo "installing essential dependencies ..."
apt-get -y install curl build-essential autoconf git-all

echo "Installing opam ..."
curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh

echo "Installing dependencies GMP, MPFR, NTL, Java, Python ..."
apt-get -y install libgmp-dev libmpfr-dev libntl-dev default-jre python

echo "Installing opam dependencies, this is going to take long ..."
opam remote add sv git://github.com/zkincaid/sv-opam.git#modern
opam install -y ocamlgraph batteries ppx_deriving z3 apron ounit menhir cil OCRS ntl

echo "Building ComPACT ... "
./configure && make

echo "Setup completed!"