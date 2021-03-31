/* Nested loop, where each with a simple *conditional* termination
   argument (step > 0). */

extern int __VERIFIER_nondet_int(void);

void foo(int step) {
  for (int i = 0; i < 4096; i += step) {
    for (int j = 0; j < 4096; j += step) {
      for (int k = 0; k < 4096; k += step) {
      }
    }
  }
}

int main(int argc, char* argv[]) {
  int step = __VERIFIER_nondet_int();
  if (step <= 0) { return 0; }
  foo(step);
  return 0;
}
