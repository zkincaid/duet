extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
int nondet_signed_int() {
  int r = __VERIFIER_nondet_int();
  __VERIFIER_assume ((-0x7fffffff - 1) <= r && r <= 0x7fffffff);
  return r;
}
signed int main()
{
  signed int i;
  signed int j;
  signed int k;
  signed int t;
  i = nondet_signed_int();
  j = nondet_signed_int();
  k = nondet_signed_int();
  for( ; !(i >= 101) && !(j >= k); k = k - 1)
  {
    i = j;
    while(!(!(i + 1 < (-0x7fffffff - 1) || 0x7fffffff < i + 1)));
    j = i + 1;
    while(!(!(k - 1 < (-0x7fffffff - 1) || 0x7fffffff < k - 1)));
  }
  return 0;
}
