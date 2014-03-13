OCAMLMAKEFILE = OCamlMakefile

include Makefile.config

RESULT = duet
SRC_DIR = src
CORE_FILES = core.ml core.mli ast.ml ast.mli hlir.ml report.ml afg.ml afg.mli \
	cfgIr.ml cfgIr.mli cmdLine.ml pa.ml pa.mli call.ml
MISC_FILES = dominator.ml region.ml
ANALYSIS_FILES = worklist.ml ai.ml exponential.ml bddpa.ml solve.ml	    \
	interproc.ml live.ml dg.ml eqLogic.ml lockLogic.ml aliasLogic.ml fspa.ml	    \
	inferFrames.ml havocPropagation.ml dependence.ml safety.ml slice.ml concDep.ml
C_FE_FILES = translateCil.ml translateCil.mli
CBP_FE_FILES = cbpAst.ml cbpParse.mli cbpParse.mly cbpLex.mll translateCbp.ml
GOTO_FE_FILES =

PACKS = cil apak datalog apron apron.boxMPQ apron.octD apron.polkaMPQ

LIBS = dynlink camlp4lib
BUDDY:=$(shell ocamlfind query buddy)
OCAMLLDFLAGS = -I +camlp4 -I $(BUDDY)
#-ccopt "-Wl,-rpath,$(BUDDY)" 
#OCAMLLDFLAGS = -I +camlp4 -I $(BUDDY) -ccopt "-Wl,-rpath,$(BUDDY)" -cclib '/usr/local/lib/libapron.a'
#OCAMLLDFLAGS = -cclib '-static -lbdd -dynamic -lz'
#OCAMLLDFLAGS = -noautolink -cclib '-static -lunix -lcamlstr -lnums -lbigarray -lbuddy_stubs -lbdd -lapron -lapron_caml -lmpfr -lgmp  -lcamlidl -dynamic -lz'
#apron.boxMPQ apron.octD apron.polkaMPQ

# -lmpfr -lgmp -lcamlidl
# -lboxMPQ -lboxMPQ_caml -loctD -loctD_caml -lpolkaMPQ -lpolkaMPQ_caml

# check for Ark
ifeq ($(ARK), yes)
ANALYSIS_FILES += induction.ml
PACKS += ark
endif

# check for GOTO frontend
ifneq ($(CBMC), no)
GOTO_FE_FILES += translateGoto.ml
INCDIRS += goto
LIBS += goto
OCAMLLDFLAGS += -cclib -lstdc++
endif



SOURCES = $(patsubst %, $(SRC_DIR)/core/%, $(CORE_FILES)) \
	$(patsubst %, $(SRC_DIR)/misc/%, $(MISC_FILES)) \
	$(patsubst %, $(SRC_DIR)/analysis/%, $(ANALYSIS_FILES)) \
	$(patsubst %, $(SRC_DIR)/frontend/c/%, $(C_FE_FILES)) \
	$(patsubst %, $(SRC_DIR)/frontend/cbp/%, $(CBP_FE_FILES)) \
	$(patsubst %, $(SRC_DIR)/frontend/goto/%, $(GOTO_FE_FILES)) \
	$(SRC_DIR)/ui.ml

all: native-code

include $(OCAMLMAKEFILE)
