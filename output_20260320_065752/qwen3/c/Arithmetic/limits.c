#include <limits.h>
//@ #include <verifast.h>

void foo(int x)
//@ requires true;
//@ ensures true;
{
    //@ assert INT_MIN <= x &*& x <= INT_MAX;
}