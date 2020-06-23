extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
int nondet_signed_int() {
  int r = __VERIFIER_nondet_int();
  __VERIFIER_assume ((-0x7fffffff - 1) <= r && r <= 0x7fffffff);
  return r;
}
signed int main()
{
  signed int x=nondet_signed_int();
  signed int debug=0;
  while(!(x >= 255))
  {
    if(!(x % 2 == 0))
    {
      while(!(!(x - 1 < (-0x7fffffff - 1) || 0x7fffffff < x - 1)));
      x = x - 1;
    }
    else
    {
      while(!(!(x + 2 < (-0x7fffffff - 1) || 0x7fffffff < x + 2)));
      x = x + 2;
    }
    if(!(debug == 0))
      x = 0;
  }
  return 0;
}
