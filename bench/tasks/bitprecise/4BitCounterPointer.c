typedef unsigned long int __CPROVER_size_t;
void * __builtin_alloca(__CPROVER_size_t);
signed int main()
{
  signed int *x0;
  void *return_value___builtin_alloca=__builtin_alloca(sizeof(signed int) );
  x0 = (signed int *)return_value___builtin_alloca;
  signed int *x1;
  void *return_value___builtin_alloca$0=__builtin_alloca(sizeof(signed int) );
  x1 = (signed int *)return_value___builtin_alloca$0;
  signed int *x2;
  void *return_value___builtin_alloca$1=__builtin_alloca(sizeof(signed int) );
  x2 = (signed int *)return_value___builtin_alloca$1;
  signed int *x3;
  void *return_value___builtin_alloca$2=__builtin_alloca(sizeof(signed int) );
  x3 = (signed int *)return_value___builtin_alloca$2;
  *x0 = 0;
  *x1 = 0;
  *x2 = 0;
  *x3 = 0;
  while(*x3 == 0)
    if(*x0 == 0)
      *x0 = 1;
    else
    {
      *x0 = 0;
      if(*x1 == 0)
        *x1 = 1;
      else
      {
        *x1 = 0;
        if(*x2 == 0)
          *x2 = 1;
        else
        {
          *x2 = 0;
          *x3 = 1;
        }
      }
    }
  return 0;
}
