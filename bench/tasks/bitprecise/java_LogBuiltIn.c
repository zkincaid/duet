extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
int nondet_signed_int() {
  int r = __VERIFIER_nondet_int();
  __VERIFIER_assume ((-0x7fffffff - 1) <= r && r <= 0x7fffffff);
  return r;
}
signed int mlog(signed int x);
signed int main()
{
  signed int return_value___VERIFIER_nondet_int=nondet_signed_int();
  signed int return_value_mlog=mlog(return_value___VERIFIER_nondet_int);
  return return_value_mlog;
}
signed int mlog(signed int x)
{
  signed int res=0;
  for( ; x >= 2; res = res + 1)
  {
    x = x / 2;
    while(!(!(res + 1 < (-0x7fffffff - 1) || 0x7fffffff < res + 1)));
  }
  return res;
}
