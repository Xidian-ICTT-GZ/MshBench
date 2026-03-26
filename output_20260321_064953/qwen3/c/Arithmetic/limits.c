//@ #include <limits.h>
#include <assert.h>

/*@ predicate dummy() = true; @*/

void foo(int x)
//@ requires true;
//@ ensures true;
{
    //@ open dummy();
    assert(INT_MIN <= x);
    assert(x <= INT_MAX);
    //@ close dummy();
}