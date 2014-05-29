#!/bin/sh

cd ark && make ark && sudo make reinstall && cd .. && cd duet && rm -f src/analysis/induction.o src/analysis/induction.cmx src/analysis/induction.cmo src/analysis/induction.cmi src/analysis/ipa.cmo src/analysis/ipa.cmi analysis/ipa.o analysis/ipa.cmx duet && make
# && cd ../errgen && make clean && make
