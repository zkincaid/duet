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
  signed int tx;
  x = nondet_signed_int();
  y = nondet_signed_int();
  z = nondet_signed_int();
  tx = nondet_signed_int();
  if(!(tx >= -1073741823) || tx >= 1073741824)
    return 0;
  else
    if(!(z >= -1073741823) || z >= 1073741824)
      return 0;
    else
      if(!(x >= -1073741823) || x >= 1073741824)
        return 0;
      else
        if(y >= 1073741824)
          return 0;
        else
        {
          do
          {
            while(!(!(x >= y) || (x >= y)));
            if(!(tx + z >= x) || !(x >= y))
              break;
            signed int return_value___VERIFIER_nondet_int=nondet_signed_int();
            if(!(return_value___VERIFIER_nondet_int == 0))
            {
              while(!(!(z - 1 < (-0x7fffffff - 1) || 0x7fffffff < z - 1)));
              z = z - 1;
              tx = x;
              x = nondet_signed_int();
              if(!(x >= -1073741823) || x >= 1073741824)
                return 0;
            }
            else
            {
              while(!(!(y + 1 < (-0x7fffffff - 1) || 0x7fffffff < y + 1)));
              y = y + 1;
            }
          }
          while((char)1);
          return 0;
        }
}
