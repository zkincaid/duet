default: errgen


#
# Variables.
#

OCAMLLEX  = ocamllex
OCAMLYACC = ocamlyacc
OCAMLC    = ocamlc -I src

INTERFACES = \
    src/ast.cmi          \
    src/parser.cmi

OBJS = \
    src/ast.cmo       \
    src/lexer.cmo     \
    src/parser.cmo    \
	src/interpret.cmo

#
# Patterns.
#

%.ml: %.mll
	$(OCAMLLEX) $<

%.ml %.mli: %.mly
	$(OCAMLYACC) $<

%.cmo: %.ml %.cmi
	$(OCAMLC) -g -c $<

%.cmi: %.mli
	$(OCAMLC) -g -c $<

#
# Compilation targets.
#

errgen: $(INTERFACES) $(OBJS)
	$(OCAMLC) -g -o  $@ $(OBJS)

src/lexer.cmo: src/lexer.ml
	$(OCAMLC) -g -c $<

src/interpret.cmo: src/interpret.ml
	$(OCAMLC) -g -c $<


#
# Cleanup.
#

clean:
	rm -f src/*.cmo src/*.cmi src/lexer.ml src/parser.ml 
