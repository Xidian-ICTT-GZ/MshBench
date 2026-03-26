#include "stdlib.h"

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}

void foo(int x)
//@ requires true;
//@ ensures true;
{
    assert(INT_MIN <= x);
    assert(x <= INT_MAX);
}