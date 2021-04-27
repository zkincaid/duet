Overview
====

The repository contains the implementation of ComPACT, a tool described in papers:

+ Termination Analysis without the Tears, Shaowei Zhu and Zachary Kincaid, PLDI 2021
+ Reflections on Termination of Linear Loops, Shaowei Zhu and Zachary Kincaid, CAV 2021

The PLDI 2021 paper describes a framework for compositional and monotone
termination analysis, and the CAV 2021 paper describes a particular analysis
that can be used in that framework. As a result, if one wants to run the tool described by the CAV
2021 paper in isolation, then one can do so by passing certain command line flags to the ComPACT
executable. 

Building and running from scratch
====

If starting out with a fresh ubuntu environment, we have provided scripts that install the required dependencies and compile ComPACT from source. We recommend using a recent ubuntu version (>= 18.04).
Download the source from https://github.com/happypig95/duet/tree/modern and run (the setup_root.sh script needs root privileges to install packages, while the setup_user.sh should not be run as root user since opam is not designed to be run as root)

```
sudo bash setup_root.sh
bash setup_user.sh
```

After ComPACT has been compiled, there will be an executable duet.exe at the root of git repository.
The full ComPACT (combining the PLDI 2021 and the CAV 2021 paper) could be run as

```
./duet.exe -termination -monotone -termination-no-attractor path/to/c/program/on/disk.c
```

For example one can run ComPACT on a benchmark program that comes with this repository:

```
./duet.exe -termination -monotone -termination-no-attractor ./bench/tasks/termination-linear/nested.c
```

The subset of ComPACT as described in the CAV paper can be run on individual C programs as

```
./duet.exe -termination -monotone -termination-no-attractor -termination-no-exp -termination-no-phase -termination-no-llrf path/to/c/program/on/disk.c
```


Source locations
====

Most relevant source files can be found in `/srk/src`.
In particular, the procedure that computes the best linear abstraction is implemented in `solvablePolynomial.ml` in the `abstract` method of the `DLTS` module. The mortal precondition operator that returns a terminating precondition for any transition formula based on the best linear abstraction is implemented in `terminationDTA.ml`.

New experiments
====
You can also write new programs to play with ComPACT. The following commands may 
be used in the source C program in addition to usual C constructs: 

```
 __VERIFIER_assume( b_expr ); 
```

 This instructs ComPACT to assume that b_expr is always true whenever control 
 reaches the assume statement. 

```
__VERIFIER_nondet_int(); 
```

 This non-deterministic function may return any (signed) integer. 
 To obtain a non-negative integer, you can write something like: 
 ```
 N = __VERIFIER_nondet_int(); 
 __VERIFIER_assume(N >= 0); 
 ```

See the benchmark programs inside /home/zsw/termination/compact/bench/tasks for 
examples of how these can be used. 

You could write any C program to try ComPACT, yet a simple benchmark program to try might look like the following

```C
int main(int argc, char* argv[]) {
  for (int i = 0; i < 20; i++) {
    for (int j = 0; j < 20; j++) {
      for (int k = 0; k < 20; k++) {
      }
    }
  }
   return 0;
}
```

Related work
====
ComPACT is implemented based on [Zachary Kincaid's previous work](https://github.com/zkincaid/duet).
