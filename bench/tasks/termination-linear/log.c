/* Computation of log_2(log_2(n)) */

extern int __VERIFIER_nondet_int(void);

int log2(int n) {
  int r = 1;
  while (r < n) { r = 2 * r; }
  return r;
}

int main(int argc, char* argv[]) {
  int n = __VERIFIER_nondet_int();
  if (n > 1000000 || n <= 0) { return 0; }
  return log2(log2(n));
}
