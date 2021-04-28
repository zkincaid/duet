#!/bin/bash
# This script will install dependencies for ComPACT.
# It should be run in ubuntu version >= 18.04.
set -e

if [ $(id -u) != "0" ]; then
echo "You must be the superuser to run this script to install packages!" >&2
exit 1
fi

# adding repository that contains the stable version of opam
add-apt-repository -y ppa:avsm/ppa
apt-get update

echo "installing essential dependencies ..."
apt-get -y install curl build-essential autoconf git-all

echo "Installing dependencies opam, GMP, MPFR, NTL, Java, Python ..."
apt-get -y install opam libgmp-dev libmpfr-dev libntl-dev default-jre python

echo "Library dependencies installation completed!"