include ../Makefile.config

OCAMLC=ocamlc
OCAMLOPT=ocamlopt
OCAMLMKLIB=ocamlmklib
CBMC_LIBS = big-int/bigint.o langapi/langapi.a xmllang/xmllang.a util/util.a \
	ansi-c/ansi-c.a pointer-analysis/pointer-analysis.a		     \
	goto-programs/goto-programs.a
LIBS = $(patsubst %, $(CBMC)/%, $(CBMC_LIBS))

all: goto.cma

goto.cmxa: goto.cma
goto.cma: goto_stubs.o goto.cmo goto.cmx
	$(OCAMLMKLIB) $(LIBS) -cclib -lstdc++ $^ -o goto

goto_stubs.o: goto_stubs.cpp
	@echo $(CBMC)
	g++ -fPIC -I $(CBMC) -I $(CBMC)/util -c $<

%.cmi: %.mli
	$(OCAMLOPT) -c $<

%.cmx: %.ml
	$(OCAMLOPT) -c $<

%.cmo: %.ml
	$(OCAMLC) -c $<

clean:
	rm -f *.a *.cm[xio] *.o *.so

# dependencies
goto.cmx: goto.cmi
goto.cmo: goto.cmi
