extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
int nondet_signed_int() {
  int r = __VERIFIER_nondet_int();
  __VERIFIER_assume ((-0x7fffffff - 1) <= r && r <= 0x7fffffff);
  return r;
}
void foo(void);
signed int x;
void foo(void)
{
  while(!(!(x - 1 < (-0x7fffffff - 1) || 0x7fffffff < x - 1)));
  x = x - 1;
}
signed int main()
{
  x = nondet_signed_int();
  while(x >= 1)
  {
    signed int return_value___VERIFIER_nondet_int=nondet_signed_int();
    if(!(return_value___VERIFIER_nondet_int == 0))
      foo();
    else
      foo();
  }
  return 0;
}
