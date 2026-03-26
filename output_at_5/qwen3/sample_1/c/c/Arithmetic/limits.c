#include <limits.h>

void foo(int x)
    
    
{
    //@ requires true;
    assert(INT_MIN <= x);
    assert(x <= INT_MAX);
    //@ ensures true;
}