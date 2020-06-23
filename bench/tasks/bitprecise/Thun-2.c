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
  x = nondet_signed_int();
  y = nondet_signed_int();
  if(!(x >= -65535) || x >= 65536)
    return 0;
  else
    if(!(y >= -65535) || y >= 65536)
      return 0;
    else
    {
      for( ; x >= 0; y = -2 * y - 1)
      {
        while(!(!(x + y < (-0x7fffffff - 1) || 0x7fffffff < x + y)));
        x = x + y;
        while(!(!(-2 * y < (-0x7fffffff - 1) || 0x7fffffff < -2 * y)));
        while(!(!(-2 * y - 1 < (-0x7fffffff - 1) || 0x7fffffff < -2 * y - 1)));
      }
      return 0;
    }
}
