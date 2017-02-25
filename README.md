Duet
====
Duet is a static analysis tool designed for analyzing concurrent programs.

Building
========

### Dependencies

Duet depends on several software packages.  The following dependencies need to be installed manually.

<<<<<<< HEAD
 + [opam](http://opam.ocaml.org) (with OCaml 4.01 & native compiler)
 + autotools
=======
 + [opam](http://opam.ocaml.org) (with OCaml >= 4.02 & native compiler)
>>>>>>> origin/ark2
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
<<<<<<< HEAD
 opam install ocamlgraph batteries cil.1.7.3 oasis deriving Z3 apron.0.9.10 ounit
=======
 opam install ocamlgraph batteries cil oasis ppx_deriving Z3 apron ounit menhir mathsat
>>>>>>> origin/ark2
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
<<<<<<< HEAD
* Compositional recurrence analysis: `duet -cra FILE`
=======
* Compositional recurrence analysis: `duet -cra FILE` (*disabled* in the ark2 branch)
* Proof spaces: `duet -proofspace FILE`
>>>>>>> origin/ark2

Duet supports two file types (and guesses which to use by file extension): C programs (.c), Boolean programs (.bp).

By default, Duet checks user-defined assertions. Alternatively, it can also instrument assertions as follows:

    duet -check-array-bounds -check-null-deref -coarsen FILE


Architecture
============
Duet is split into several packages:

* apak

  Algebraic program analysis kit.  This is a collection of utilities for implementing program analyzers.  It contains various graph algorithms (e.g., fixpoint computation, path expression algorithms) and utilities for constructing algebraic structures.

* ark 

<<<<<<< HEAD
  Arithmetic reasoning kit.  This is a high-level interface over Z3 and Apron.  Most of the work of compositional recurrence analysis lives in ark.
=======
  Arithmetic reasoning kit.  This is a high-level interface over Z3, MathSAT and Apron.  Most of the work of compositional recurrence analysis lives in ark.

* pa

  Predicate automata library.
>>>>>>> origin/ark2

* duet

  Implements program analyses, frontends, and anything programming-language specific.
