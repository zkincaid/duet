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

    if (y>0) {
	while(x<100) {
	    x=x+y;
	}
    }
           
    assert(y<=0 || (y>0 && x>=100));    
}


