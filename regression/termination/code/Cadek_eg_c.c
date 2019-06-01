void main()
{
	int n = __VERIFIER_nondet_int();
	__VERIFIER_assume(n >= 0);
	int x = __VERIFIER_nondet_int();
	__VERIFIER_assume(x >= 0);
	__VERIFIER_assume(x <= n);
	int c = 0, y = 3;

	while (x > 0)
	{
		x--;
		c++;
		if (__VERIFIER_nondet_int())
			y = c;
		__VERIFIER_assert((c >= 0) && (c <= n));
		__VERIFIER_assert((y == 3) || (y == c ));
	}
	// __VERIFIER_assert((3 > n || y <= 3) && (3 <= n || y <= n));
}
