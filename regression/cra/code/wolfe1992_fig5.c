// Source: Michael Wolfe: Beyond Induction Variables, PLDI 1992.

void main() {
  int j,k,l,t;
  __VERIFIER_assume(j != k);
  __VERIFIER_assume(j != l);
  __VERIFIER_assume(k != l);
  while(__VERIFIER_nondet_int()) {
    t = j;
    j = k;
    k = l;
    l = t;
  }
  __VERIFIER_assert(j != k);
  __VERIFIER_assert(j != l);
  __VERIFIER_assert(k != l);

}
