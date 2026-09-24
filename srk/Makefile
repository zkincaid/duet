.PHONY: build test

all: build

build:
	dune build

clean:
	dune clean

test:
	dune exec test/test_srk.exe

install:
	dune build @install
	dune install

uninstall:
	dune uninstall

doc:
	dune build @doc
