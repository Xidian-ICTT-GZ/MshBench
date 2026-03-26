void foo(int x)
//@ requires INT_MIN <= x &*& x <= INT_MAX;
//@ ensures true;
{
    
    assert(INT_MIN <= x);
    assert(x <= INT_MAX);
}