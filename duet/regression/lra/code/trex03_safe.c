void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: goto ERROR;
  }
  return;
}
unsigned int __VERIFIER_nondet_uint();
_Bool __VERIFIER_nondet_bool();

int main()
{
    unsigned int x1=rand(), x2=rand(), x3=rand();
  unsigned int d1=1, d2=1, d3=1;
  int c1=rand(), c2=rand();
  assume(x1 >= 0);
  assume(x2 >= 0);
  assume(x3 >= 0);
  
  while(x1>0 && x2>0 && x3>0)
  {
    if (c1) x1=x1-d1;
    else if (c2) x2=x2-d2;
    else x3=x3-d3;
    c1=rand();
    c2=rand();
  }

  assert(x1==0 || x2==0 || x3==0);
  return 0;
}

