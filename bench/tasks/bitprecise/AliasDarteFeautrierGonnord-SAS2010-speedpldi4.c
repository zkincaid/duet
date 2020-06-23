extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
int nondet_signed_int() {
  int r = __VERIFIER_nondet_int();
  __VERIFIER_assume ((-0x7fffffff - 1) <= r && r <= 0x7fffffff);
  return r;
}
signed int main()
{
  signed int i;
  signed int m;
  signed int n=nondet_signed_int();
  m = nondet_signed_int();
  if(m >= 1 && !(m >= n))
  {
    i = n;
    while(i >= 1)
      if(!(i >= m))
      {
        while(!(!(i - 1 < (-0x7fffffff - 1) || 0x7fffffff < i - 1)));
        i = i - 1;
      }
      else
      {
        while(!(!(i - m < (-0x7fffffff - 1) || 0x7fffffff < i - m)));
        i = i - m;
      }
  }
  return 0;
}
