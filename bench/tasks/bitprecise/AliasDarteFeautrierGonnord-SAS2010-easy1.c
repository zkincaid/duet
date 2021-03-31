extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
int nondet_signed_int() {
  int r = __VERIFIER_nondet_int();
  __VERIFIER_assume ((-0x7fffffff - 1) <= r && r <= 0x7fffffff);
  return r;
}
signed int main()
{
  signed int x=0;
  signed int y=100;
  signed int z=nondet_signed_int();
  while(!(x >= 40))
    if(z == 0)
    {
      while(!(!(x + 1 < (-0x7fffffff - 1) || 0x7fffffff < x + 1)));
      x = x + 1;
    }
    else
    {
      while(!(!(x + 2 < (-0x7fffffff - 1) || 0x7fffffff < x + 2)));
      x = x + 2;
    }
  return 0;
}
