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
  signed int x;
  signed int y;
  signed int z;
  x = nondet_signed_int();
  y = nondet_signed_int();
  z = nondet_signed_int();
  c = 0;
  do
  {
    while(!(!(y >= 0) || (y >= 0)));
    while(!(!(!(y >= 0 && z < 2147483647 - y) && y < 0) || (!(y >= 0 && z < 2147483647 - y) && y < 0)));
    while(!(!(y >= 0 && z < 2147483647 - y || y < 0 && (signed long int)z > -2147483648l - (signed long int)y) || (y >= 0 && z < 2147483647 - y || y < 0 && (signed long int)z > -2147483648l - (signed long int)y)));
    if(y + z >= x || y >= 2147483647 || z >= 2147483647 || (!(y >= 0) || z >= 2147483647 + -y) && (-2147483648l + -((signed long int)y) >= (signed long int)z || y >= 0))
      break;
    while(!(!(y + 1 < (-0x7fffffff - 1) || 0x7fffffff < y + 1)));
    y = y + 1;
    while(!(!(z + 1 < (-0x7fffffff - 1) || 0x7fffffff < z + 1)));
    z = z + 1;
  }
  while((char)1);
  return 0;
}
