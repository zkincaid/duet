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
  signed int z;
  signed int i;
  x = nondet_signed_int();
  y = nondet_signed_int();
  z = 0;
  i = x;
  if(x >= 1 && y >= 1)
  {
    for( ; i >= 1; z = z + 1)
    {
      while(!(!(i - 1 < (-0x7fffffff - 1) || 0x7fffffff < i - 1)));
      i = i - 1;
      while(!(!(z + 1 < (-0x7fffffff - 1) || 0x7fffffff < z + 1)));
    }
    for( ; !(i >= y); z = z - 1)
    {
      while(!(!(i + 1 < (-0x7fffffff - 1) || 0x7fffffff < i + 1)));
      i = i + 1;
      while(!(!(z - 1 < (-0x7fffffff - 1) || 0x7fffffff < z - 1)));
    }
  }
  return 0;
}
