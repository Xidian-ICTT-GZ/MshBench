void foo(int x)
    //@ requires true;
    //@ ensures true;
    
{
    //@ open true;
    assert(INT_MIN <= x);
    assert(x <= INT_MAX);
}