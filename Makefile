SETUP = ocaml setup.ml

all: build

.PHONY: build duet srk apak patools test cca config

build: setup.ml setup.data
	$(SETUP) -build

duet: setup.ml setup.data duet/config.ml
	ocamlbuild duet/duet.native

newton: config
	ocamlbuild duet/libduet.cmx
	ocamlbuild -use-ocamlfind -tag 'runtime_variant(_pic)' duet/libduet.native.so

srk: setup.ml setup.data
	ocamlbuild srk/src/test_srk.native -tag debug

apak: setup.ml setup.data
	ocamlbuild apak/test_apak.native -tag debug

patools: setup.ml setup.data
	ocamlbuild patools/patools.native -tag debug

setup.ml: _oasis
	oasis setup

config:
	./configure

setup.data: setup.ml
	$(SETUP) -configure

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
