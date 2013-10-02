all: regression

ROOT = ..
EXTRA_SRC = cfg/cfgRegression.ml bt/btRegression.ml regression.ml
EXTRA_DIRS = bt cfg
include $(ROOT)/Makefile.include

regression: $(OBJS_CMX)
	$(OCAMLOPT) $(LINK_FLAGS) $(LIBS) $(OBJS_CMX) -o regression

clean:
	rm -f regression.cmx regression.o
	rm -f cfg/cfgRegression.cmx cfg/cfgRegression.o
	rm -f bt/btRegression.cmx bt/btRegression.o
