extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
int nondet_signed_int() {
  int r = __VERIFIER_nondet_int();
  __VERIFIER_assume ((-0x7fffffff - 1) <= r && r <= 0x7fffffff);
  return r;
}
signed int main()
{
  signed int c;
  signed int x;
  signed int y;
  x = nondet_signed_int();
  y = nondet_signed_int();
  c = 0;
  do
  {
    while(!(!(x >= 0) || (x >= 0)));
    while(!(!(!(x >= 0 && y < 2147483647 - x) && x < 0) || (!(x >= 0 && y < 2147483647 - x) && x < 0)));
    while(!(!(x >= 0 && y < 2147483647 - x || x < 0 && (signed long int)y > -2147483648l - (signed long int)x) || (x >= 0 && y < 2147483647 - x || x < 0 && (signed long int)y > -2147483648l - (signed long int)x)));
    if(!(x + y >= 1) || (!(x >= 0) || y >= 2147483647 + -x) && (-2147483648l + -((signed long int)x) >= (signed long int)y || x >= 0))
      break;
    if(x >= 1)
    {
      while(!(!(x - 1 < (-0x7fffffff - 1) || 0x7fffffff < x - 1)));
      x = x - 1;
    }
    else
      if(y >= 1)
      {
        while(!(!(y - 1 < (-0x7fffffff - 1) || 0x7fffffff < y - 1)));
        y = y - 1;
      }
  }
  while((char)1);
  return 0;
}
