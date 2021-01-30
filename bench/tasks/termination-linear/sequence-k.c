/* Sequential composition of loops, each with a simple *conditional*
   termination argument */

extern int __VERIFIER_nondet_int(void);

void foo(int step) {
  for (int i = 0; i < 4096; i += step) ;
  for (int i = 0; i < 4096; i += step) ;
  for (int i = 0; i < 4096; i += step) ;
}

int main(int argc, char* argv[]) {
  int step = __VERIFIER_nondet_int();
  if (step <= 0) { return 0; }
  foo(step);
  return 0;
}
