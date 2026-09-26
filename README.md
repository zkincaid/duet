Duet
====
Duet is a static analysis tool designed for analyzing concurrent programs.

Building
========

### Dev container

The easiest way to get a working build environment is the dev container in
`.devcontainer/`.  It is an Ubuntu 24.04 image with OCaml 5.4.0 and all of
Duet's dependencies pre-installed.

To use it with [VS Code](https://code.visualstudio.com/), install
[Docker](https://www.docker.com/) and the
[Dev Containers](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-containers)
extension, open the repository, and run *Dev Containers: Reopen in Container*
from the command palette.  The first build compiles the OCaml dependencies
from source, so it takes a while; later starts reuse the cached image.

You can also use the dev containter without VS Code.  From the root of
the repository, build the image (named `duet-dev`) with
```
 docker build -t duet-dev -f .devcontainer/Dockerfile .devcontainer
```
and then start a shell in it, with your checkout of the repository mounted
at `/workspace`:
```
 docker run -it --rm -v "$PWD":/workspace -w /workspace duet-dev bash -l
```
Changes you make under `/workspace` are made directly to your checkout, so
you can edit files on the host and build inside the container.

Inside the container, build Duet as described in [Building Duet](#building-duet).

### Dependencies

To set up a build environment without the dev container, install the following dependencies manually.

 + [opam](http://opam.ocaml.org) (version >= 2, with OCaml >= 4.10 & native compiler)
   - If you have an older version of opam installed, you can install opam2 using `opam install opam-devel`
 + A C compiler, make, and m4
 + GMP and MPFR
 + Java
 + Python 3
 + Libffi
 + Pkg-config
 + Autoconf
 + Libtool
 + [Flint](https://flintlib.org/)
 + [MSolve](https://msolve.lip6.fr/) (optional)

On Ubuntu, you can install these packages with:
```
 sudo apt-get install build-essential m4 opam libgmp-dev libmpfr-dev default-jre python3 python-is-python3 libffi-dev pkg-config autoconf libtool libflint-dev msolve
```

The `msolve` package is available in Ubuntu 24.04 and newer.  On older Ubuntu
releases, install it from source using the instructions in the
[msolve repository](https://github.com/algebraic-solving/msolve).

On MacOS, you can install these packages (except Java) with:
```
 brew install opam gmp mpfr python libffi pkg-config autoconf libtool flint msolve
```

Next, add the [sv-opam](https://github.com/zkincaid/sv-opam) OPAM repository, and install the rest of duet's dependencies.  These are built from source, so grab a coffee &mdash; this may take a long time.
```
 opam remote add sv https://github.com/zkincaid/sv-opam.git
 opam install dune zarith ocamlgraph batteries ppx_deriving ounit menhir ctypes-foreign
 opam install cil apron normalizffi flint.dev faugere.dev z3
```

Duet can optionally use msolve to accelerate Gröbner-basis computations.  The
`msolve` executable must be available on `PATH`; alternatively, set the
`MSOLVE` environment variable to its path.  Duet uses msolve by default; pass
`-no-msolve` to use its built-in Buchberger implementation instead.


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

Typically, it is best to run CRA with `-cra-split-loops`.  By default, the `-cra` runs the analysis as described in POPL'18.  Running `-cra` with the `-monotone` flag gives essentially a simplified version of the FMCAD'15 analysis.

Several other analyses are available using the `-cra-X` family of flags (see `./duet.exe --help` for a full list).
* `-cra-prsd`: Zachary Kincaid, Jason Breck, John Cyphert, and Tom Reps: [Closed Forms for Numerical Loops](https://www.cs.princeton.edu/~zkincaid/pub/popl19a.pdf).  POPL 2019.
* `-cra-vas` and `-cra-vass`: Jake Silverman and Zachary Kincaid: [Loop Summarization with Rational Vector Addition Systems](https://www.cs.princeton.edu/~zkincaid/pub/cav19.pdf).  CAV 2019.
* `-lirr`: Zachary Kincaid, Nicolas Koh, Shaowei Zhu: *When Less is More: Consequence-finding in a Weak Theory of Arithmetic*.  POPL 2023.
* `-lirr-sp`, `-lirr-usp`, and `-lirr-sp-quad`: John Cyphert and Zachary Kincaid: [Solvable Polynomial Ideals: The Ideal Reflection for Program Analysis](https://www.cs.princeton.edu/~zkincaid/pub/popl24.pdf).  POPL 2024.

### Algebraic termination analysis

The `-termination` flag implements algebraic termination analysis, as described in
* Shaowei Zhu, Zachary Kincaid: [Termination Analysis Without the Tears](https://www.cs.princeton.edu/~zkincaid/pub/pldi21.pdf). PLDI 2021.
* Shaowei Zhu, Zachary Kincaid: [Reflections on Termination of Linear Loops](https://www.cs.princeton.edu/~zkincaid/pub/cav21.pdf). CAV 2021.
* Shaowei Zhu, Zachary Kincaid: [Breaking the Mold: Nonlinear Ranking Function Synthesis Without Templates](https://www.cs.princeton.edu/~zkincaid/_static/pub/cav24b.pdf). CAV 2024.

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
