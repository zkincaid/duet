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
      while(!(!(x + y < (-0x7fffffff - 1) || 0x7fffffff < x + y)));
      if(!(x + y >= 1))
        for( ; x >= 1; y = y - 1)
        {
          while(!(!(x + x < (-0x7fffffff - 1) || 0x7fffffff < x + x)));
          while(!(!(x + x + y < (-0x7fffffff - 1) || 0x7fffffff < x + x + y)));
          x = x + x + y;
          while(!(!(y - 1 < (-0x7fffffff - 1) || 0x7fffffff < y - 1)));
        }
      return 0;
    }
}
