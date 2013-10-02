#							-*-makefile-gmake-*-
OCAMLMAKEFILE = OCamlMakefile
ANNOTATE = "yes"

SOURCES = buddy.ml buddy.mli libbuddy_stubs.c
RESULT  = buddy
# Only install the files that exist, the default OCamlMakefile tries
# to install the native code ones even on arch with no native code support.
LIBINSTALL_FILES = $(wildcard *.mli *.cmi *.cma *.cmx *.cmxa *.a *.so)
INCDIRS = 
LIBS =  
CLIBS =  bdd
CFLAGS = -g -O2 -DHAVE_STRERROR_R
#CFLAGS += -DWANT_DEBUG

.PHONY: all byte opt install uninstall update
all: byte opt
byte: byte-code-library
opt: native-code-library

install: libinstall
uninstall: libuninstall
update: uninstall install

include $(OCAMLMAKEFILE)
