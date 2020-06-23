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
  if(x >= 1)
    do
    {
      while(!(!(x > y) || (x > y)));
      if(!(2147483647 + -x >= y) || y >= x)
        break;
      while(!(!(y + x < (-0x7fffffff - 1) || 0x7fffffff < y + x)));
      y = y + x;
    }
    while((char)1);
  return 0;
}
