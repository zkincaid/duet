.PHONY: build test

all: build

build:
	dune build

clean:
	dune clean

test:
	dune runtest -f

install:
	dune build @install
	dune install

uninstall:
	dune uninstall

doc:
	dune build @doc
