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
  signed int y;
  signed int tx=nondet_signed_int();
  x = nondet_signed_int();
  y = nondet_signed_int();
  if(tx >= 1073741824)
    return 0;
  else
    if(x >= 1073741824)
      return 0;
    else
      if(!(y >= -1073741823))
        return 0;
      else
      {
        while(tx >= 0 && x >= y)
        {
          signed int return_value___VERIFIER_nondet_int=nondet_signed_int();
          if(!(return_value___VERIFIER_nondet_int == 0))
          {
            while(!(!(x - 1 < (-0x7fffffff - 1) || 0x7fffffff < x - 1)));
            while(!(!(-1 + x - tx < (-0x7fffffff - 1) || 0x7fffffff < -1 + x - tx)));
            x = (x - 1) - tx;
          }
          else
          {
            while(!(!(y + 1 < (-0x7fffffff - 1) || 0x7fffffff < y + 1)));
            while(!(!(1 + y + tx < (-0x7fffffff - 1) || 0x7fffffff < 1 + y + tx)));
            y = y + 1 + tx;
          }
        }
        return 0;
      }
}
