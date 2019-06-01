void main()
{
	int n = __VERIFIER_nondet_int();
	__VERIFIER_assume(n >= 0);
	int x = __VERIFIER_nondet_int();
	__VERIFIER_assume(n >= x);
	int m = __VERIFIER_nondet_int();
	__VERIFIER_assume(m >= 0);
	int y = 0, c = 0;

	while (x > 0)
	{
		x--;
		y = m;
		while (y > 0)
		{
			y--;
			c++;
		}
	}

	__VERIFIER_assert(c <= m * n);
}
