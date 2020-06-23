extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
int nondet_signed_int() {
  int r = __VERIFIER_nondet_int();
  __VERIFIER_assume ((-0x7fffffff - 1) <= r && r <= 0x7fffffff);
  return r;
}
signed int main()
{
  signed int q;
  signed int y;
  q = nondet_signed_int();
  y = nondet_signed_int();
  while(q >= 1)
    if(y >= 1)
    {
      while(!(!(q - y < (-0x7fffffff - 1) || 0x7fffffff < q - y)));
      while(!(!(q + -y - 1 < (-0x7fffffff - 1) || 0x7fffffff < q + -y - 1)));
      q = (q - y) - 1;
    }
    else
    {
      while(!(!(q + y < (-0x7fffffff - 1) || 0x7fffffff < q + y)));
      while(!(!(q + y - 1 < (-0x7fffffff - 1) || 0x7fffffff < q + y - 1)));
      q = (q + y) - 1;
    }
  return 0;
}
