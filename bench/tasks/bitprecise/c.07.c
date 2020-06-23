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
  signed int i;
  signed int j;
  signed int k;
  signed int tmp;
  i = nondet_signed_int();
  j = nondet_signed_int();
  k = nondet_signed_int();
  tmp = nondet_signed_int();
  c = 0;
  for( ; k >= j && (signed long int)k >= -2147483647l && !(i >= 101); k = k - 1)
  {
    tmp = i;
    i = j;
    while(!(!(tmp + 1 < (-0x7fffffff - 1) || 0x7fffffff < tmp + 1)));
    j = tmp + 1;
    while(!(!(k - 1 < (-0x7fffffff - 1) || 0x7fffffff < k - 1)));
  }
  return 0;
}
