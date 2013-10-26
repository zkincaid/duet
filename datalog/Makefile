OCAMLMAKEFILE = OCamlMakefile

RESULT = datalog
SRC = datalogCore.ml datalogParser.ml rename.ml interpreter.ml incremental.ml \
	datalog.ml ui.ml

SOURCES = $(patsubst %, src/%, $(SRC))
PACKS = ocamlgraph deriving apak buddy camlp4.lib
ROOT=/home/zkincaid/src/duet-project
BUDDY:=$(shell ocamlfind query buddy)
OCAMLLDFLAGS = -I +camlp4 -I $(BUDDY) -ccopt "-Wl,-rpath,$(BUDDY)"

all: native-code byte-code native-code-library byte-code-library

install: src/datalog.cmi datalog.cma datalog.cmxa datalog.a
	ocamlfind install datalog META $^

uninstall: libuninstall

reinstall:
	make uninstall
	make install

include $(OCAMLMAKEFILE)
