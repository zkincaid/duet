Duet
====
Duet is a static analysis tool designed for analyzing concurrent programs.

Building
========

Duet depends on several software packages.  Some of the more obscure dependencies are managed by the setup script.  The following dependencies need to be installed manually.

 + autoconf
 + OCaml (>= 3.12, with native compiler)
 + camlp4
 + CamlIDL
 + findlib
 + Java
 + GMP (+ ocaml bindings)
 + MPFR (+ ocaml bindings)
 + libbdd
 + z3 4.3.1 (+ its ocaml bindings, beware of http://z3.codeplex.com/workitem/29)

Building Duet:

Once the all dependencies have been installed, 

Run `sudo ./setup.sh <username>`


Documentation can be built with `make doc` the output will be in `./doc`.  This requires ocamldoc.  A dependency graph of the modules in the project can be built with `make dg`; the output will be in `doc/dependencies.png`.

A TAGS file (for emacs/vim) can be built with `make tags`.  This requires `otags`.

Running Duet
============

There are three main program analyses implemented in Duet:

* Data flow graphs (POPL'12): `duet -coarsen FILE`
* Heap data flow graphs: `duet -hdfg FILE`
* Linear recurrence analysis: `duet -lra FILE`

Duet supports two file types (and guesses which to use by file extension): C programs (.c), Boolean programs (.bp).

By default, Duet checks user-defined assertions. Alternatively, it can also instrument assertions as follows:

    duet -check-array-bounds -check-null-deref -coarsen FILE


Architecture
============
Duet is split into several modules:

* deriving

  Extension to OCaml for deriving functions from type declarations.  This extends the original [deriving](https://github.com/jaked/deriving) package with a `Compare` class.

* buddy

  Bindings to the [BuDDy](http://buddy.sourceforge.net/manual/main.html) binary decision diagram (BDD) package.  This extends the original [bindings](https://github.com/abate/ocaml-buddy) with some additional functions.

* datalog

  BDD-based datalog implementation and interface to [bddbddb](http://bddbddb.sourceforge.net)

* apak

  Algebraic program analysis kit.  This is a collection of utilities for implementing program analyzers.  It contains various graph algorithms (e.g., fixpoint computation, path expression algorithms) and utilities for constructing algebraic structures.

* ark 

  Arithmetic reasoning kit.  This is a high-level interface over Z3 (and eventually Apron).  Most of the work of linear recurrence analysis lives in ark.

* duet

  Implements program analyses, frontends, and anything programming-language specific.
