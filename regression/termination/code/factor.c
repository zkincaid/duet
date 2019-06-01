void main() { 
    int i, n=__VERIFIER_nondet_int();
    __VERIFIER_assume(n >= 2);
    for(i=2; i % n != 0; i++)
	;
    __VERIFIER_assert(i <= n); // safe but currently unprovable
}
