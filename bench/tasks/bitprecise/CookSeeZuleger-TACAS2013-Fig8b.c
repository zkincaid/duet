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
  signed int M;
  x = nondet_signed_int();
  M = nondet_signed_int();
  if(M >= 1)
    while(!(x == M))
      if(!(M >= x))
        x = 0;
      else
      {
        while(!(!(x + 1 < (-0x7fffffff - 1) || 0x7fffffff < x + 1)));
        x = x + 1;
      }
  return 0;
}
