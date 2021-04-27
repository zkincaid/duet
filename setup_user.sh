#!/bin/bash
# This script will install dependencies then build ComPACT
# It should be run in ubuntu version >= 18.04.
set -e

echo "Checking opam version ..."
opam_ver="$(opam --version)"
required_opam_ver="2.0.0"
 if [ "$(printf '%s\n' "$requiredver" "$currentver" | sort -V | head -n1)" = "$requiredver" ]; then 
        echo "opam version >= 2.0, OK"
 else
        echo "Your distribution does not have opam 2 binaries, you need to install opam manually https://opam.ocaml.org/doc/Install.html"
        exit 1
 fi

echo "Setting up opam ..."
opam init -y 
if ! opam switch list | grep -q '4.10.0'; then
    opam switch create 4.10.0
fi
opam init -y
eval `opam config env`

echo "Installing opam dependencies, this is going to take long ..."
opam remote add sv git://github.com/zkincaid/sv-opam.git#modern
opam install -y dune ocamlgraph batteries ppx_deriving z3 apron ounit menhir cil OCRS ntl

echo "Compiling ComPACT ... "
./configure
make

if test -f "./duet.exe"; then
    echo "Setup successful!"
else
    echo "Setup failed ..."
    exit 1
fi
