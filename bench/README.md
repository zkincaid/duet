Bench
=====

This directory contains [benchexec](https://github.com/sosy-lab/benchexec)
scripts to simplify benchmarking and generating tables and plots.


Building
--------

Prior to using `bench.py`,

1. [benchexec](https://github.com/sosy-lab/benchexec) must be installed.
2. Any additional tools must be available in `PATH` so that benchexec can find them.

Note that `benchexec` may require that several permissions be set
before it can execute.

Usage
-----

`bench.py` has the following commands

* `run`
   Runs selected tools on selected benchmark suites.  By default, runs are cached.
   * `--timeout` specifies timeout in seconds
   * `--no-cache` forces the run, even if a result is in the cache
* `scatter`
   Generate scatter plot data along with accompanying LaTeX code.  Two tools must be
   specified using `--tools`
* `cactus`
   Generate cactus plot data along with accompanying LaTeX code
* `table`
   Generate html benchmark data
* `summary`
   Generate summary data along as a LaTeX table

All commands can be configured with the flags

* `--tools TOOL1,TOOL2,...`
* `--suites SUITE1,SUITE2,...`

which specify the set of tools and suites, respectively.

### Sample usage

 Run CRA and VASS on the C4B and HOLA suites, with a timeout of 30 seconds:

```
 ./bench.py run --tools CRA,VASS --suites C4B,HOLA --timeout 30
```

 Scatter plot of CRA vs VASS on the C4B suite

```
 ./bench.py scatter --tools CRA,VASS --suites C4B
```

 Generate LaTeX table for all available tools and all available suites

```
 ./bench.py summary
```

Tools and suites
----------------

Benchmarks are defined in the `benchmark-defs` directory.  Each tool
`TOOL` has a corresponding `TOOL.xml` file, the format of which is
described
[here](https://github.com/sosy-lab/benchexec/blob/master/doc/benchexec.md).
Each `TOOL.xml` should define a set of task suites (`tasks`).
`bench.py` can run `TOOL` on a `SUITE` only if `TOOL.xml` defines a
task suite named `SUITE`.

Benchmark tasks should be defined by [YAML](https://yaml.org/) files,
formatted according to [benchexec specifications](https://github.com/sosy-lab/benchexec/blob/master/doc/task-definition-example.yml)

Suite descriptions
------------------

* Termination: check termination for the non-recursive, terminating
  benchmarks f rom SV-COMP20 Termination-MainControlFlow.set
* Nontermination: check termination for the non-terminating benchmarks
  from SV-COMP20 Termination-MainControlFlow.set + the recursive
  folder
* recursive: check termination for the recursive, terminating
  benchmarks from SV-COMP20 Termination-MainControlFlow.set + the
  recursive folder
* polybench: check termination for the [Polyhedral Benchmark
  suite](https://web.cse.ohio-state.edu/~pouchet.2/software/polybench/)
* bitprecise: bit-precise variation of the Termination suite, minus
  two benchmarks for which Ultimate Automizer was able to prove
  non-termination (java_AG313 and SyntaxSupportPointer01-3).
