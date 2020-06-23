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
    for( ; !(x == 0) && !(x == -1); x = x - 2)
      while(!(!(x - 2 < (-0x7fffffff - 1) || 0x7fffffff < x - 2)));
  return 0;
}
