SETUP = ocaml setup.ml

all: build

.PHONY: build duet ark apak patools test cca

build: setup.ml setup.data
	$(SETUP) -build

duet: setup.ml setup.data duet/config.ml
	ocamlbuild duet/duet.native -tag debug

srk: setup.ml setup.data
	ocamlbuild srk/src/test_srk.native -tag debug

apak: setup.ml setup.data
	ocamlbuild apak/test_apak.native -tag debug

patools: setup.ml setup.data
	ocamlbuild patools/patools.native -tag debug

cca: setup.ml setup.data
	ocamlbuild cca/cca.native -tag debug

setup.ml: _oasis
	oasis setup

setup.data: setup.ml
	$(SETUP) -configure --enable-tests

install:
	$(SETUP) -install

clean:
	$(SETUP) -clean
	@rm -f setup.data

test:
	$(SETUP) -test

uninstall:
	$(SETUP) -uninstall

reinstall:
	$(SETUP) -reinstall

doc: setup.ml setup.data
	$(SETUP) -doc
