extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
int nondet_signed_int() {
  int r = __VERIFIER_nondet_int();
  __VERIFIER_assume ((-0x7fffffff - 1) <= r && r <= 0x7fffffff);
  return r;
}
signed int main()
{
  signed int x=nondet_signed_int();
  if(x >= 1)
    for( ; !(x == 0); x = x - 1)
      while(!(!(x - 1 < (-0x7fffffff - 1) || 0x7fffffff < x - 1)));
  return 0;
}
