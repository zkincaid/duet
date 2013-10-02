OCAMLMAKEFILE = OCamlMakefile

SRC = putil.mli putil.ml log.ml sig.ml monoid.ml monoid.mli semilattice.ml \
	semilattice.mli lattice.ml lattice.mli ka.ml enumeration.ml	   \
	disjointSet.ml evalLink.ml memo.ml memo.mli dll.mli dll.ml	   \
	extGraph.ml extGraph.mli loop.ml loop.mli fixpoint.ml fixpoint.mli \
	recGraph.ml recGraph.mli sese.ml sese.mli pathexp.ml pathexp.mli   \
	regex.ml persistent.ml tagged.ml tagged.mli
TEST_SRC := $(SRC) test_memo.ml test_sese.ml test_regex.ml test_pathexp.ml \
	test_recgraph.ml

export OCAMLFLAGS = -annot
export PACKS = ocamlgraph deriving batteries oUnit
export LIB_PACK_NAME = apak

define PROJ_apak
  SOURCES = $(patsubst %, src/%, $(SRC))
  RESULT = apak
endef
export PROJ_apak

define PROJ_test
  SOURCES = $(patsubst %, src/%, $(TEST_SRC)) unit_test.ml
  RESULT = test
endef
export PROJ_test

ifndef SUBPROJS
  export SUBPROJS = apak test
endif

all: test apak

test:
	@$(MAKE) -f $(OCAMLMAKEFILE) subprojs SUBPROJS=test SUBTARGET=native-code

apak:
	@$(MAKE) -f $(OCAMLMAKEFILE) subprojs SUBPROJS=apak SUBTARGET="native-code-library byte-code-library"

install:
	ocamlfind install apak META apak.cmi apak.cma apak.cmxa \
	apak.a

uninstall:
	@$(MAKE) -f $(OCAMLMAKEFILE) subprojs SUBPROJS=apak SUBTARGET=libuninstall

reinstall:
	make uninstall
	make install
%:
	@$(MAKE) -f $(OCAMLMAKEFILE) subprojs SUBTARGET=$@
.PHONY: test
