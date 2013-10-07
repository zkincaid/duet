OCAMLMAKEFILE = OCamlMakefile

#LIB_PACK_NAME = ark

SRC = hashcons.mli hashcons.ml hset.mli hset.ml hmap.mli hmap.ml	  \
	arkPervasives.ml smt.ml numDomain.ml linear.ml term.ml formula.ml \
	transition.ml
TEST_SRC := $(SRC) test_formula.ml test_numdomain.ml test_transition.ml test.ml

Z3:=$(shell ocamlfind query z3)

export PACKS = deriving apak apron apron.boxMPQ apron.octD apron.polkaMPQ z3 \
	oUnit
export OCAMLFLAGS = -annot
export OCAMLLDFLAGS = -cclib -L$(Z3) -cclib -lz3 -cclib -lz3stubs
export LIBS = dynlink
export LIB_PACK_NAME = ark

define PROJ_ark
  SOURCES = $(patsubst %, src/%, $(SRC))
  RESULT = ark
endef
export PROJ_ark

define PROJ_test
  SOURCES = $(patsubst %, src/%, $(TEST_SRC))
  RESULT = test
endef
export PROJ_test

ifndef SUBPROJS
  export SUBPROJS = ark test
endif

all: test ark

test:
	@$(MAKE) -f $(OCAMLMAKEFILE) subprojs SUBPROJS=test SUBTARGET=native-code

ark:
	@$(MAKE) -f $(OCAMLMAKEFILE) subprojs SUBPROJS=ark SUBTARGET="native-code-library byte-code-library"


install:
	ocamlfind install ark META ark.cmi ark.cma ark.cmxa ark.a

uninstall:
	@$(MAKE) -f $(OCAMLMAKEFILE) subprojs SUBPROJS=ark SUBTARGET=libuninstall

reinstall:
	make uninstall
	make install

%:
	@$(MAKE) -f $(OCAMLMAKEFILE) subprojs SUBTARGET=$@

.PHONY: test
