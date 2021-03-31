extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
int nondet_signed_int() {
  int r = __VERIFIER_nondet_int();
  __VERIFIER_assume ((-0x7fffffff - 1) <= r && r <= 0x7fffffff);
  return r;
}
signed int main()
{
  signed int p;
  signed int q=nondet_signed_int();
  p = nondet_signed_int();
  while(p >= 1 && q >= 1 && !(p == q))
    if(!(q >= p))
    {
      while(!(!(q - 1 < (-0x7fffffff - 1) || 0x7fffffff < q - 1)));
      q = q - 1;
      p = nondet_signed_int();
    }
    else
      if(!(p >= q))
      {
        while(!(!(p - 1 < (-0x7fffffff - 1) || 0x7fffffff < p - 1)));
        p = p - 1;
        q = nondet_signed_int();
      }
  return 0;
}
