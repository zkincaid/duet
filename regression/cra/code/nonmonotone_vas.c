void main() {
  int x = 0;
  while(__VERIFIER_nondet_int()) {
    if (__VERIFIER_nondet_int()) {
      x = x + 2;
    } else {
      x = x + 4;
    }
  }
  __VERIFIER_assert(x % 2 == 0);
}
