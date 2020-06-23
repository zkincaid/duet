extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
int nondet_signed_int() {
  int r = __VERIFIER_nondet_int();
  __VERIFIER_assume ((-0x7fffffff - 1) <= r && r <= 0x7fffffff);
  return r;
}
void f(signed int d);
void f(signed int d)
{
  signed int x=nondet_signed_int();
  signed int y=nondet_signed_int();
  signed int k=nondet_signed_int();
  signed int z=1;
  if(!(k >= 1073741824))
  {
  L1:
    ;
    for( ; !(z >= k); z = 2 * z)
      while(!(!(2 * z < (-0x7fffffff - 1) || 0x7fffffff < 2 * z)));
  L2:
    ;
    while(x >= 1 && y >= 1)
    {
      signed int return_value___VERIFIER_nondet_int=nondet_signed_int();
      if(!(return_value___VERIFIER_nondet_int == 0))
      {
      P1:
        ;
        while(!(!(x - d < (-0x7fffffff - 1) || 0x7fffffff < x - d)));
        x = x - d;
        y = nondet_signed_int();
        while(!(!(z - 1 < (-0x7fffffff - 1) || 0x7fffffff < z - 1)));
        z = z - 1;
      }
      else
      {
        while(!(!(y - d < (-0x7fffffff - 1) || 0x7fffffff < y - d)));
        y = y - d;
      }
    }
  }
}
signed int main()
{
  signed int return_value___VERIFIER_nondet_int=nondet_signed_int();
  if(!(return_value___VERIFIER_nondet_int == 0))
    f(1);
  else
    f(2);
}
