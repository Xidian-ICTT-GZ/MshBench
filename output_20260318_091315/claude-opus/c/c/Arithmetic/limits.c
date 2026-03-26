#include <limits.h>

void foo(int x)
//@ requires true;
//@ ensures true;
{
    //@ assert INT_MIN <= x;
    assert(INT_MIN <= x);
    //@ assert x <= INT_MAX;
    assert(x <= INT_MAX);
}