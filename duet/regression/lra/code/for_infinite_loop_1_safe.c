extern void __VERIFIER_assume(int);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: goto ERROR;
  }
  return;
}

int __VERIFIER_nondet_int();

int main() {
  int i=0, x=0, y=0;
  int n=rand();
  assume(n>0);
  for(i=0; 1; i++)
  {
    assert(x==0);
  }
  assert(x==0);
}

