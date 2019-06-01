void main()
{
	int x = __VERIFIER_nondet_int();
	__VERIFIER_assume(x >= 0);
	int i = 0, j = 0;
	while (i < x)
	{
		i++;
		j = j + i;
	}
	__VERIFIER_assert(2 * j <= x * (x - 1));
}