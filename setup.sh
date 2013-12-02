#!/bin/bash

set -e

duet_web=http://duet.cs.toronto.edu/depend

if [[ $# -ne 1 || $UID -ne 0 ]]; then
    echo "Usage: setup.sh <username>"
    echo "    Builds Duet from source.  This must be run as root, but the files created"
    echo "    by this script will be owned by <username>."
    echo "    The following packages are required, but not managed by this script:"
    echo "    - OCaml (>= 3.12, with native compiler)"
    echo "    - camlp4"
    echo "    - CamlIDL"
    echo "    - findlib"
    echo "    - Java"
    echo "    - Darcs"
    echo "    - GMP"
    echo "    - MPFR"
    echo "    - libbdd"
    exit 1
fi
user=$1

ensure_package () {
    package=$1
    if [ ! -d "`ocamlfind query $package 2>&1`" ]; then
	if [ ! -d "depend" ]; then
	    sudo -u $user mkdir depend
	fi
	cd depend
	sudo -u $user wget $duet_web/$package.tgz
	sudo -u $user tar -zxf $package.tgz
	cd $package && ./setup.sh $user
	cd ../..
    fi
}

# Install camlp4find
if [ -z `which camlp4find` ]; then
    sudo -u $user wget $duet_web/camlp4find
    chmod +x camlp4find
    echo -n "Location to install camlp4find [default /usr/local/bin]: "
    read INSTALL_PATH
    if [ -z "$INSTALL_PATH" ]; then
	INSTALL_PATH=/usr/local/bin
    fi
    echo Installing to $INSTALL_PATH
    mv camlp4find $INSTALL_PATH/
fi

# Build and install dependencies
ensure_package oUnit
ensure_package ocamlgraph
ensure_package cil
ensure_package gmp
ensure_package apron
ensure_package camomile
ensure_package batteries



for p in deriving buddy apak datalog ark; do
	pushd $p
	sudo -u $user make && make install
	popd
done

# Build Duet
cd duet
sudo -u $user autoconf
sudo -u $user ./configure #--with-ark
sudo -u $user make
cd ..
