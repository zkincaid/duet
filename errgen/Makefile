OCAMLMAKEFILE = OCamlMakefile

RESULT = approx
SRC_DIR = src
FILES = ast.ml ast.mli lexer.mll parser.mli parser.mly approx.ml
SOURCES = $(patsubst %, $(SRC_DIR)/%, $(FILES))
PACKS = ark

all: native-code

include $(OCAMLMAKEFILE)
