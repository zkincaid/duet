void main()
{
    int x = __VERIFIER_nondet_int();
    int c = 1;
    __VERIFIER_assume(x <= 100);
    while (c > 0)
    {
        if (x > 100)
        {
            x = x - 10;
            c = c - 1;
        }
        else
        {
            x = x + 11;
            c = c + 1;
        }
    }
    __VERIFIER_assert(x == 91);
}