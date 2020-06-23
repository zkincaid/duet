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
  i = 0;
  j = 5;
  for( ; !(i >= 100); i = i + 1)
    while(!(!(i + 1 < (-0x7fffffff - 1) || 0x7fffffff < i + 1)));
  for( ; !(j >= 21); j = j + 3)
    while(!(!(j + 3 < (-0x7fffffff - 1) || 0x7fffffff < j + 3)));
  return 0;
}
