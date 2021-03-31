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
  signed int y;
  signed int random;
  x = nondet_signed_int();
  y = nondet_signed_int();
  while(x >= 1 && y >= 1)
  {
    random = nondet_signed_int();
    if(!(random >= 42))
    {
      while(!(!(x - 1 < (-0x7fffffff - 1) || 0x7fffffff < x - 1)));
      x = x - 1;
      random = nondet_signed_int();
      y = random;
    }
    else
    {
      while(!(!(y - 1 < (-0x7fffffff - 1) || 0x7fffffff < y - 1)));
      y = y - 1;
    }
  }
  return 0;
}
