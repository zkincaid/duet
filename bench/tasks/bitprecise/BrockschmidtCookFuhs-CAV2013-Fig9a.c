extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
int nondet_signed_int() {
  int r = __VERIFIER_nondet_int();
  __VERIFIER_assume ((-0x7fffffff - 1) <= r && r <= 0x7fffffff);
  return r;
}
signed int main()
{
  signed int k;
  signed int i;
  signed int j;
  signed int n;
  k = nondet_signed_int();
  i = nondet_signed_int();
  j = nondet_signed_int();
  n = nondet_signed_int();
  if(k >= 1)
  {
    i = 0;
    for( ; !(i >= n); i = i + 1)
    {
      j = 0;
      for( ; i >= j; j = j + k)
        while(!(!(j + k < (-0x7fffffff - 1) || 0x7fffffff < j + k)));
      while(!(!(i + 1 < (-0x7fffffff - 1) || 0x7fffffff < i + 1)));
    }
  }
  return 0;
}
