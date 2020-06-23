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
  signed int oldx;
  x = nondet_signed_int();
  y = nondet_signed_int();
  if(!(x >= -1073741823) || x >= 1073741824)
    return 0;
  else
    if(!(y >= -1073741823) || y >= 1073741824)
      return 0;
    else
    {
      for( ; x >= 0 || y >= 0; y = oldx - 1)
      {
        oldx = x;
        while(!(!(y - 1 < (-0x7fffffff - 1) || 0x7fffffff < y - 1)));
        x = y - 1;
        while(!(!(oldx - 1 < (-0x7fffffff - 1) || 0x7fffffff < oldx - 1)));
      }
      return 0;
    }
}
