extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
int nondet_signed_int() {
  int r = __VERIFIER_nondet_int();
  __VERIFIER_assume ((-0x7fffffff - 1) <= r && r <= 0x7fffffff);
  return r;
}
signed int f(signed int k, signed int l);
signed int f(signed int k, signed int l)
{
  signed int i=0;
  signed int j=0;
L1:
  ;
  while((char)1)
  {
    if(!(i >= k))
    {
      while(!(!(i + 1 < (-0x7fffffff - 1) || 0x7fffffff < i + 1)));
      i = i + 1;
      if(!(i % 2 == 0))
        goto L1;
    }
  L2:
    ;
    if(j >= l)
      goto __CPROVER_DUMP_L5;
    while(!(!(j + 1 < (-0x7fffffff - 1) || 0x7fffffff < j + 1)));
    j = j + 1;
    if(!(i % 2 == 0))
      break;
  }
  goto L2;
__CPROVER_DUMP_L5:
  ;
  while(!(!(i + j < (-0x7fffffff - 1) || 0x7fffffff < i + j)));
  return i + j;
}
signed int main()
{
  signed int return_value___VERIFIER_nondet_int=nondet_signed_int();
  signed int return_value___VERIFIER_nondet_int$0=nondet_signed_int();
  signed int return_value_f=f(return_value___VERIFIER_nondet_int, return_value___VERIFIER_nondet_int$0);
  return return_value_f;
}
