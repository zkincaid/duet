SETUP = ocaml setup.ml

all: build

.PHONY: build duet ark apak patools

build: setup.ml setup.data
	$(SETUP) -build

duet: setup.ml setup.data duet/src/config.ml
	ocamlbuild duet/src/duet.native -tag debug
	cp duet.native duet/duet

ark: setup.ml setup.data
	ocamlbuild ark/test_ark.native -tag debug

apak: setup.ml setup.data
	ocamlbuild apak/test_apak.byte -tag debug

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
