srk
====

Srk (symbolic reasoning kit) is a library for reasoning about logical
formulas.  Documentation for the srk API can be found
[here](http://cs.princeton.edu/~zkincaid/srk/doc/index.html).  An outline of
the main functionality implemented in the library:

 + `Iteration`: approximate transitive closure of transition relations.
   Described in
   [FMCAD:FK2015](http://www.cs.princeton.edu/~zkincaid/pub/fmcad15.pdf) and
   [POPL:KCBR2018](http://www.cs.princeton.edu/~zkincaid/pub/popl2018a.pdf).
 + `Quantifier.simsat`: evidence-producing SMT solver for the theories LRA and LIA (with quantifiers).  Described in [IJCAI:FK2016](http://www.cs.princeton.edu/~zkincaid/pub/ijcai16.pdf).  The procedure `simsat_forward` is an improved algorithm that should be preferred in most circumstances.
 + `Quantifier.winning_strategy`: strategy-synthesis procedure described in Section 4 of [POPL:FK2018](http://www.cs.princeton.edu/~zkincaid/pub/popl18b.pdf).  (The procedure described in Section 5 can be found [here](https://github.com/zkincaid/strategy-improvement))
 + `Wedge`: wedge abstract domain.  Described in section 4 of [POPL:KCBR2018](http://www.cs.princeton.edu/~zkincaid/pub/popl2018a.pdf)
 + `Abstract`: symbolic abstraction routines (over-approximate a formula by a property in some abstract domain)
 + `Nonlinear.linearize`: Formula linearization (over-approximate a formula with non-linear arithmetic by one with only linear arithmetic).  Described in Section IV of [FMCAD:FK2015](http://www.cs.princeton.edu/~zkincaid/pub/fmcad15.pdf).

Srk also provides an interface to several other libraries, including
 + [Z3](https://github.com/Z3Prover/z3): SMT solver
 + [Apron](http://apron.cri.ensmp.fr/library): numerical abstract domain library
 + [FLINT](https://flintlib.org/): fast library for number theory
 + [msolve](https://github.com/algebraic-solving/msolve): Gröbner bases and polynomial system solving (optional)

References
----------
+ IJCAI:FK2016: Azadeh Farzan and Zachary Kincaid: [Linear Arithmetic Satisfiability via Strategy Improvement](http://www.cs.princeton.edu/~zkincaid/pub/ijcai16.pdf).  IJCAI 2016.
+ POPL:FK2018: Azadeh Farzan and Zachary Kincaid: [Strategy Synthesis for Linear Arithmetic Games](http://www.cs.princeton.edu/~zkincaid/pub/popl18b.pdf).  POPL 2018.
+ POPL:KCBR2018: Zachary Kincaid, John Cyphert, Jason Breck, and Thomas Reps: [Non-Linear Reasoning For Invariant Synthesis](http://www.cs.princeton.edu/~zkincaid/pub/popl2018a.pdf).  POPL 2018.
+ FMCAD:FK2015: Azadeh Farzan and Zachary Kincaid: [Compositional Recurrence Analysis](http://www.cs.princeton.edu/~zkincaid/pub/fmcad15.pdf).  FMCAD 2015.

Building
========

### Dependencies

Srk depends on several software packages.  The following dependencies need to be installed manually.

 + [opam](http://opam.ocaml.org) (with OCaml >= 4.10 & native compiler)
   - If you have an older version of opam installed, you can install opam2 using `opam install opam-devel`
 + A C compiler, make, and m4
 + [GMP and MPFR](https://gmplib.org/)
 + Python 3
 + Libffi
 + Pkg-config
 + Flint

On Ubuntu, you can install these packages with:
```
 sudo apt-get install build-essential m4 opam libgmp-dev libmpfr-dev python3 python-is-python3 libffi-dev pkg-config libflint-dev msolve
```

The `msolve` package is available in Ubuntu 24.04 and newer.  On older Ubuntu
releases, install it from source using the instructions in the
[msolve repository](https://github.com/algebraic-solving/msolve).

On MacOS, you can install these packages with:
```
 brew install opam gmp mpfr python libffi pkg-config flint msolve
```

Next, add the [sv-opam](https://github.com/zkincaid/sv-opam) OPAM repository, and install the rest of srk's dependencies.  These are built from source, so grab a coffee &mdash; this may take a long time.
```
 opam remote add sv https://github.com/zkincaid/sv-opam.git
 opam install dune zarith ocamlgraph batteries ppx_deriving ounit menhir ctypes-foreign
 opam install apron normalizffi flint.dev z3
```

Duet can optionally use msolve to accelerate Gröbner-basis computations.  The
`msolve` executable must be available on `PATH`; alternatively, set the
`MSOLVE` environment variable to its path.  Srk uses msolve by default to
accelerate Gröbner-basis computations; set `Ideal.use_msolve := false` to use
the built-in Buchberger implementation for ideal computations instead (srk
also falls back to Buchberger when msolve cannot be found).  The implementation of
number fields **requires** msolve.
setting does not affect number-field operations: `NumberField.primitive_elem`
and `NumberField.splitting_field` **requires** msolve.

### Building srk

After srk's dependencies are installed, it can be built with `make`.  Srk's makefile has the following targets:
 + `make`: Build srk and `bigtop` command-line utility.
 + `make doc`: Build documentation
 + `make test`: Run test suite

Running srk
===========

The srk library is packaged with a command-line utility `bigtop` that can be
used to access some of its functionality.  Documentation for running `bigtop`
can found by executing `bigtop.exe -h`.
