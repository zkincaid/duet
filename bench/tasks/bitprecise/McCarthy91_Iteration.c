extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
int nondet_signed_int() {
  int r = __VERIFIER_nondet_int();
  __VERIFIER_assume ((-0x7fffffff - 1) <= r && r <= 0x7fffffff);
  return r;
}
signed int main()
{
  signed int c;
  signed int n;
  c = 1;
  n = nondet_signed_int();
  while(c >= 1)
    if(n >= 101)
    {
      while(!(!(n - 10 < (-0x7fffffff - 1) || 0x7fffffff < n - 10)));
      n = n - 10;
      while(!(!(c - 1 < (-0x7fffffff - 1) || 0x7fffffff < c - 1)));
      c = c - 1;
    }
    else
    {
      while(!(!(n + 11 < (-0x7fffffff - 1) || 0x7fffffff < n + 11)));
      n = n + 11;
      while(!(!(c + 1 < (-0x7fffffff - 1) || 0x7fffffff < c + 1)));
      c = c + 1;
    }
  return 0;
}
