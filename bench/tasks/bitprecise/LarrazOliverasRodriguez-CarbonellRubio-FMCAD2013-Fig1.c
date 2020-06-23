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
  x = nondet_signed_int();
  y = nondet_signed_int();
  z = nondet_signed_int();
  if(x >= -10000 && !(x >= 10001) && !(y >= 10001) && !(z >= 10001))
    for( ; y >= 1; y = x + y)
    {
      while(!(!(x - 1 < (-0x7fffffff - 1) || 0x7fffffff < x - 1)));
      x = x - 1;
      for( ; !(y >= z); z = z - 1)
      {
        while(!(!(x + 1 < (-0x7fffffff - 1) || 0x7fffffff < x + 1)));
        x = x + 1;
        while(!(!(z - 1 < (-0x7fffffff - 1) || 0x7fffffff < z - 1)));
      }
      while(!(!(x + y < (-0x7fffffff - 1) || 0x7fffffff < x + y)));
    }
  return 0;
}
