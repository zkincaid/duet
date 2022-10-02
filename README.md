Duet
====
Duet is a static analysis tool designed for analyzing concurrent programs.

Building
========

### Dependencies

Duet depends on several software packages.  The following dependencies need to be installed manually.

 + [opam](http://opam.ocaml.org) (version >= 2, with OCaml >= 4.10 & native compiler)
   - If you have an older version of opam installed, you can install opam2 using `opam install opam-devel`
 + GMP and MPFR
 + [NTL](http://www.shoup.net/ntl/): number theory library
 + Java
 + Python

On Ubuntu, you can install these packages with:
```
 sudo apt-get install opam libgmp-dev libmpfr-dev libntl-dev default-jre python
```

On MacOS, you can install these packages (except Java) with:
```
 brew install opam gmp mpfr ntl python
```

Next, add the [sv-opam](https://github.com/zkincaid/sv-opam) OPAM repository, and install the rest of duet's dependencies.  These are built from source, so grab a coffee &mdash; this may take a long time.
```
 opam remote add sv https://github.com/zkincaid/sv-opam.git#modern
 opam install ocamlgraph batteries ppx_deriving z3 apron ounit menhir cil OCRS ntl normalizffi
```

### Building Duet

After Duet's dependencies are installed, it can be built as follows:
```
 ./configure
 make
```

Duet's makefile has the following targets:
 + `make`: Build duet
 + `make srk`: Build the ark library and test suite
 + `make apak`: Build the apak library and test suite
 + `make doc`: Build documentation
 + `make test`: Run test suite

Running Duet
============

There are three main program analyses implemented in Duet:

* Data flow graphs: `duet.native -coarsen FILE`
* Proof spaces: `duet.native -proofspace FILE`
* Compositional recurrence analysis: `duet.native -cra FILE`

Duet supports two file types (and guesses which to use by file extension): C programs (.c), Boolean programs (.bp).

By default, Duet checks user-defined assertions, which are specified by the built-in function `__VERIFIER_assert`. Alternatively, it can also instrument assertions as follows:

    duet.native -check-array-bounds -check-null-deref -coarsen FILE


### Data flow graphs

The `-coarsen` flag implements an invariant generation procedure for multi-threaded programs with an unbounded number of threads. The analysis is described in
* Azadeh Farzan and Zachary Kincaid: [Verification of Parameterized Concurrent Programs By Modular Reasoning about Data and Control](http://www.cs.princeton.edu/~zkincaid/pub/popl12.pdf).  POPL 2012.

### Proof spaces

The `-proofspace` flag implements a software model checking procedure for multi-threaded programs with an unbounded number of threads.  The procedure is described in
* Azadeh Farzan, Zachary Kincaid, Andreas Podelski: [Proof Spaces for Unbounded Parallelism](http://www.cs.princeton.edu/~zkincaid/pub/popl15.pdf).  POPL 2015.

### Compositional recurrence analysis

The `-cra` flag is an invariant generation procedure for sequential programs.  The analysis is described in
* Azadeh Farzan and Zachary Kincaid: [Compositional Recurrence Analysis](http://www.cs.princeton.edu/~zkincaid/pub/fmcad15.pdf).  FMCAD 2015.
* Zachary Kincaid, John Cyphert, Jason Breck, Thomas Reps: [Non-Linear Reasoning For Invariant Synthesis](http://www.cs.princeton.edu/~zkincaid/pub/popl18a.pdf).  POPL 2018.

Typically, it is best to run CRA with `-cra-split-loops`.  By default, the `-cra` runs the analysis as described in POPL'18.  The FMCAD'15 analysis can be run by setting the `-cra-no-matrix` flag.

Several other analyses are available using the `-cra-X` family of flags (see `./duet.exe --help` for a full list).
* `-cra-prsd`: Zachary Kincaid, Jason Breck, John Cyphert, and Tom Rep: [Closed Forms for Numerical Loops](https://www.cs.princeton.edu/~zkincaid/pub/popl19a.pdf).  POPL 2019.
* `-cra-vas` and `-cra-vass`: Jake Silverman and Zachary Kincaid: [Loop Summarization with Rational Vector Addition Systems](https://www.cs.princeton.edu/~zkincaid/pub/cav19.pdf).  CAV 2019.
* `-lirr`: Zachary Kincaid, Nicolas Koh, Shaowei Zhu: *When Less is More: Consequence-finding in a Weak Theory of Arithmetic*.  To appear in POPL 2023.

The interprocedural variant is described in
* Zachary Kincaid, Jason Breck, Ashkan Forouhi Boroujeni, Thomas Reps:  [Compositional Recurrence Analysis Revisited](http://www.cs.princeton.edu/~zkincaid/pub/pldi17.pdf). PLDI 2017.

is available in the *Newton-ark2* branch of this repository.  Build instructions to come.

### Algebraic termination analysis

The `-termination` flag implements algebraic termination analysis, as described in
* Shaowei Zhu, Zachary Kincaid: [Termination Analysis Without the Tears](https://www.cs.princeton.edu/~zkincaid/pub/pldi21.pdf). PLDI 2021.
* Reflections on Termination of Linear Loops: [Reflections on Termination of Linear Loops](https://www.cs.princeton.edu/~zkincaid/pub/cav21.pdf). CAV 2021.

By default, the termination analyzer uses a portfolio of different approaches
for proving termination, which can be selectively disabled using the
`-termination-no-X` family of flags (see `./duet.exe --help` for a full list).
Most of the `-cra-X` family of flags are also compatible with `-termination`.

Architecture
============
Duet is split into several packages:

* srk 

  Symbolic reasoning kit.  This is a high-level interface over Z3 and Apron.  Most of the work of compositional recurrence analysis lives in srk.

* pa

  Predicate automata library.

* duet

  Implements program analyses, frontends, and anything programming-language specific.
