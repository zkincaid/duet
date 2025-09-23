procedure GotoExample(x: int) returns (y: int)
{
    y := 0;

    if (x > 0) {
        goto Positive;
    } else {
        goto Negative;
    }

Positive:
    y := x + 1;
    return;

Negative:
    y := x - 1;
    return;
}