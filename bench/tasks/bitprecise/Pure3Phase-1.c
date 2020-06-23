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
  signed int z;
  x = nondet_signed_int();
  y = nondet_signed_int();
  z = nondet_signed_int();
  if(x >= 65536)
    return 0;
  else
    if(!(y >= -65535) || y >= 65536)
      return 0;
    else
      if(!(z >= -65535) || z >= 65536)
        return 0;
      else
      {
        while(x >= 0)
        {
          signed int return_value___VERIFIER_nondet_int=nondet_signed_int();
          if(!(return_value___VERIFIER_nondet_int == 0))
          {
            while(!(!(x + y < (-0x7fffffff - 1) || 0x7fffffff < x + y)));
            x = x + y;
          }
          else
          {
            while(!(!(x + z < (-0x7fffffff - 1) || 0x7fffffff < x + z)));
            x = x + z;
          }
          while(!(!(y + z < (-0x7fffffff - 1) || 0x7fffffff < y + z)));
          y = y + z;
          while(!(!(z - 1 < (-0x7fffffff - 1) || 0x7fffffff < z - 1)));
          z = z - 1;
        }
        return 0;
      }
}
