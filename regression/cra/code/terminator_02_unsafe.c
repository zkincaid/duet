void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: goto ERROR;
  }
  return;
}
int __VERIFIER_nondet_int();
_Bool __VERIFIER_nondet_bool();

void main()
{
    int x=rand();
    int y=rand();
    int z=rand();

    while(x<100 && 100<z) {
	int tmp=rand();
	if (tmp) {
	    x++;
	} else {
	    x--;
	    z--;
	}
    }                 
    
    assert(0);    
}


