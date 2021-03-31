/* Nested loop, where each loop has a simple termination argument. */

extern int __VERIFIER_nondet_int(void);

int main(int argc, char* argv[]) {
  for (int i = 0; i < 4096; i++) {
    for (int j = 0; j < 4096; j++) {
      for (int k = 0; k < 4096; k++) {
      }
    }
  }
  return 0;
}
