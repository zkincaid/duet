#VERSION = $(shell git describe --tags --always)
VERSION = 0.1.1a-git

target: obuild

built:
	$(MAKE) -C syntax
	$(MAKE) -C lib ncl bcl

.PHONY: tests
tests: built
	$(MAKE) -C tests

clean:
	$(MAKE) -C syntax clean
	$(MAKE) -C lib clean
	$(MAKE) -C tests clean

.PHONY: obuild
obuild:
	ocamlbuild deriving.cma deriving.cmxa deriving.byte deriving.native

.PHONY: install
install: obuild
	ocamlfind install -patch-version $(VERSION) \
	deriving META \
	$(wildcard _build/*.cmxa _build/*.a _build/*.lib _build/*.cma) \
	$(wildcard _build/lib/*.cmi _build/lib/*.mli _build/lib/*.cmx)

.PHONY: uninstall
uninstall:
	ocamlfind remove deriving

.PHONY: oclean
oclean:
	ocamlbuild -clean

