void main()
{
	int n = __VERIFIER_nondet_int();
	__VERIFIER_assume(n >= 0);
	int c = 0;
	int r = n;
	int y = n;
	int x = 0;
	while (y > 0)
	{

		x = r;
		while (y > 0 && __VERIFIER_nondet_int())
		{
			x++;
			y--;
		}
		while (x > 0 && __VERIFIER_nondet_int())
		{
			x--;
			r--;
			c++;
		}
		y--;
		__VERIFIER_assert(c <= 2 * n);
	}
	// __VERIFIER_assert(c <= 2 * n);
}