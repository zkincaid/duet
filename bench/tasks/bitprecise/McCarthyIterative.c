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
  signed int c;
  x = nondet_signed_int();
  c = 1;
  while(c >= 1)
    if(x >= 101)
    {
      while(!(!(x - 10 < (-0x7fffffff - 1) || 0x7fffffff < x - 10)));
      x = x - 10;
      while(!(!(c - 1 < (-0x7fffffff - 1) || 0x7fffffff < c - 1)));
      c = c - 1;
    }
    else
    {
      while(!(!(x + 11 < (-0x7fffffff - 1) || 0x7fffffff < x + 11)));
      x = x + 11;
      while(!(!(c + 1 < (-0x7fffffff - 1) || 0x7fffffff < c + 1)));
      c = c + 1;
    }
  return 0;
}
