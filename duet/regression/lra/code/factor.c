void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: goto ERROR;
  }
  return;
}

extern int __VERIFIER_nondet_int();
void main() { 
    int i, n=rand();
    assume(n >= 2);
    for(i=2; i % n != 0; i++)
	;
    assert(i <= n);
}
