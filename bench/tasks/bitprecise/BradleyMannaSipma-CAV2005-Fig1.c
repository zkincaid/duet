extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
int nondet_signed_int() {
  int r = __VERIFIER_nondet_int();
  __VERIFIER_assume ((-0x7fffffff - 1) <= r && r <= 0x7fffffff);
  return r;
}
signed int main()
{
  signed int y1;
  signed int y2;
  y1 = nondet_signed_int();
  y2 = nondet_signed_int();
  if(y1 >= 1 && y2 >= 1)
    while(!(y1 == y2))
      if(!(y2 >= y1))
      {
        while(!(!(y1 - y2 < (-0x7fffffff - 1) || 0x7fffffff < y1 - y2)));
        y1 = y1 - y2;
      }
      else
      {
        while(!(!(y2 - y1 < (-0x7fffffff - 1) || 0x7fffffff < y2 - y1)));
        y2 = y2 - y1;
      }
  return 0;
}
