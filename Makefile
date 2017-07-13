SETUP = ocaml setup.ml

all: build

.PHONY: build duet ark apak patools test

build: setup.ml setup.data
	rm -rf _build/pa/pa.a
	$(SETUP) -build

duet: setup.ml setup.data duet/config.ml
	ocamlbuild duet/duet.native -tag debug

ark: setup.ml setup.data
	ocamlbuild ark/test_ark.native -tag debug

apak: setup.ml setup.data
	ocamlbuild apak/test_apak.native -tag debug

patools: setup.ml setup.data
	ocamlbuild patools/patools.native -tag debug

setup.ml: _oasis
	oasis setup

setup.data: setup.ml
	$(SETUP) -configure --enable-tests

install:
	$(SETUP) -install

clean:
	$(SETUP) -clean

test:
	$(SETUP) -test

uninstall:
	$(SETUP) -uninstall

reinstall:
	$(SETUP) -reinstall

doc: setup.ml setup.data
	$(SETUP) -doc
