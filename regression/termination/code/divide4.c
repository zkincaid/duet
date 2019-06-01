void main() {
  int n;
  n = __VERIFIER_nondet_int();
  __VERIFIER_assume(n > 0);
  int i;
  int w, x, y, z;
  x = w = y = z = 0;
  for (i = 0; i < n; i++) {
    int tmp = z + 1;
    z = y;
    y = x;
    x = w;
    w = tmp;
  }
  __VERIFIER_assert(z == n/4);
}
