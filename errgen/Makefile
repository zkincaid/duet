OCAMLMAKEFILE = OCamlMakefile

RESULT = errgen
SRC_DIR = src
FILES = ast.ml ast.mli lexer.mll parser.mli parser.mly interpret.ml
SOURCES = $(patsubst %, $(SRC_DIR)/%, $(FILES))
PACKS = ark

all: native-code

include $(OCAMLMAKEFILE)
