//@ requires true;
//@ ensures true;
void foo(int x)
{
    assert(INT_MIN <= x);
    assert(x <= INT_MAX);
}