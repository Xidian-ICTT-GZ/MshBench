#include <limits.h>
#include <assert.h>

void foo(int x)
    //@ requires true;
    //@ ensures true;
{
    assert(INT_MIN <= x);
    assert(x <= INT_MAX);
}