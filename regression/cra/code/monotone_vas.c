void main() {
  int x = 0;
  int y;
  while(__VERIFIER_nondet_int) {
    y = __VERIFIER_nondet_int();
    __VERIFIER_assume(0 <= y && y <= 1);
    x = x + 2*y;
  }
  __VERIFIER_assert(x % 2 == 0);
}
