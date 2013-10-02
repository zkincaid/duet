all: ../duet

ROOT=..
UNIT_TESTS = util/test_regex.ml util/test_kleene.ml util/test_memo.ml	\
	unit_test.ml
EXTRA_SRC = ui.ml diff.ml $(UNIT_TESTS)
EXTRA_DIRS =
include $(ROOT)/Makefile.include

UNIT_TESTS_CMX=$(UNIT_TESTS:.ml=.cmx)

../duet: $(OBJS_CMX) ui.cmx
	$(OCAMLOPT) $(LINK_FLAGS) -o $@ $(LIBS) $^

../duet-diff: $(OBJS_CMX) diff.cmx
	$(OCAMLOPT) $(LINK_FLAGS) -o $@ $(LIBS) $^

clean:
	(for d in $(SRC_DIRS); do \
	 rm -f $$d/*.cm[iox] $$d/*.o; \
	 done)

doc: $(GENERATED)
	$(OCAMLDOC) $(OFLAGS) -html -d $(DOC) -hide Pervasives $(SRC_ML) \
	 $(SRC_MLI)

dg: $(GENERATED)
	$(OCAMLDOC) -dot -o $(DOC)/dependencies.dot -hide Pervasives $(SRC_ML)
	dot -Tpng $(DOC)/dependencies.dot -o $(DOC)/dependencies.png 


../test: $(OBJS_CMX) $(UNIT_TESTS_CMX)
	$(OCAMLOPT) $(LINK_FLAGS) -o $@ $(LIBS) oUnit.cmx $^
