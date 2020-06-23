signed int main()
{
  signed int x=nondet_signed_int();
  for( ; x >= 1; x = x / 2)
    ;
  return 0;
}
