#!/bin/bash
# This script will install dependencies then build ComPACT
# It should be run in ubuntu version >= 18.04.
set -e

if [ $(id -u) != "0" ]; then
echo "You must be the superuser to run this script" >&2
exit 1
fi

if [ $SUDO_USER ]; then
    real_user=$SUDO_USER
else
    real_user=$(whoami)
fi

# adding repository that contains the stable version of opam
add-apt-repository -y ppa:avsm/ppa
apt-get update

echo "installing essential dependencies ..."
apt-get -y install curl build-essential autoconf git-all

echo "Installing dependencies opam, GMP, MPFR, NTL, Java, Python ..."
apt-get -y install opam libgmp-dev libmpfr-dev libntl-dev default-jre python

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
sudo -u $real_user opam init -y 
sudo -u $real_user opam switch create 4.10.0
sudo -u $real_user opam init -y
eval `opam config env`

echo "Installing opam dependencies, this is going to take long ..."
sudo -u $real_user opam remote add sv git://github.com/zkincaid/sv-opam.git#modern
sudo -u $real_user opam install -y dune ocamlgraph batteries ppx_deriving z3 apron ounit menhir cil OCRS ntl

echo "Compiling ComPACT ... "
sudo -u $real_user ./configure
sudo -u $real_user make

if test -f "./duet.exe"; then
    echo "Setup successful!"
else
    echo "Setup failed ..."
    exit 1
fi
