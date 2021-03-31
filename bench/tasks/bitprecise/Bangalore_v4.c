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
  if(!(x >= y))
    for( ; x >= 0; x = x - y)
      while(!(!(x - y < (-0x7fffffff - 1) || 0x7fffffff < x - y)));
  return 0;
}
