void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: goto ERROR;
  }
  return;
}
unsigned int __VERIFIER_nondet_uint();

void main()
{
    unsigned int n = rand();
    assume(n >= 0);
    unsigned int x=n, y=0;
    while(x>0) {
	x--;
	y++;
    }
    assert(y==n);
}

