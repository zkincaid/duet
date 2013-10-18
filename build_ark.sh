#!/bin/sh

cd ark && make ark && sudo make reinstall && cd .. && cd duet && rm -f src/analysis/induction.o src/analysis/induction.cmx src/analysis/induction.cmo src/analysis/induction.cmi && make && cd ../errgen && make clean && make
