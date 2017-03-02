Duet
====
Duet is a static analysis tool designed for analyzing concurrent programs.

Building
========

### Dependencies

Duet depends on several software packages.  The following dependencies need to be installed manually.

 + [opam](http://opam.ocaml.org) (with OCaml >= 4.02 & native compiler)
 + GMP and MPFR
 + [MathSAT](http://mathsat.fbk.eu)

On Ubuntu, you can install these packages (except Java and MathSAT) with:
```
 sudo apt-get install opam libgmp-dev libmpfr-dev
```

On MacOS, you can install these packages (except Java and MathSAT) with:
```
 brew install opam gmp mpfr
```

Next, add the [sv-opam](https://github.com/zkincaid/sv-opam) OPAM repository, and install the rest of duet's dependencies.  These are built from source, so grab a coffee &mdash; this may take a long time.
```
 opam remote add sv git://github.com/zkincaid/sv-opam.git
 opam install ocamlgraph batteries cil oasis ppx_deriving Z3 apron ounit menhir mathsat OCRS
```

### Building Duet

After Duet's dependencies are installed, it can be built as follows:
```
 ./configure
 make
```

Duet's makefile has the following targets:
 + `make`: Build duet
 + `make ark`: Build the ark library and test suite
 + `make apak`: Build the apak library and test suite
 + `make doc`: Build documentation
 + `make test`: Run test suite

Running Duet
============

There are three main program analyses implemented in Duet:

* Data flow graphs (POPL'12): `duet -coarsen FILE`
* Heap data flow graphs: `duet -hdfg FILE`
* Compositional recurrence analysis: `duet -cra FILE`
* Proof spaces: `duet -proofspace FILE`

Duet supports two file types (and guesses which to use by file extension): C programs (.c), Boolean programs (.bp).

By default, Duet checks user-defined assertions. Alternatively, it can also instrument assertions as follows:

    duet -check-array-bounds -check-null-deref -coarsen FILE


Architecture
============
Duet is split into several packages:

* apak

  Algebraic program analysis kit.  This is a collection of utilities for implementing program analyzers.  It contains various graph algorithms (e.g., fixpoint computation, path expression algorithms) and utilities for constructing algebraic structures.

* ark 

  Arithmetic reasoning kit.  This is a high-level interface over Z3, MathSAT and Apron.  Most of the work of compositional recurrence analysis lives in ark.

* pa

  Predicate automata library.

* duet

  Implements program analyses, frontends, and anything programming-language specific.
