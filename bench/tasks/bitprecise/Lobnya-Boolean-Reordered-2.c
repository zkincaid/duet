extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
int nondet_signed_int() {
  int r = __VERIFIER_nondet_int();
  __VERIFIER_assume ((-0x7fffffff - 1) <= r && r <= 0x7fffffff);
  return r;
}
signed int main()
{
  signed int x;
  signed int b;
  x = nondet_signed_int();
  b = nondet_signed_int();
  if(!(x >= -2147483647))
    return 0;
  else
  {
    while(!(b == 0))
    {
      b = nondet_signed_int();
      while(!(!(x - 1 < (-0x7fffffff - 1) || 0x7fffffff < x - 1)));
      x = x - 1;
      if(x >= 0)
        b = 1;
      else
        b = 0;
    }
    return 0;
  }
}
