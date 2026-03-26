/*@ predicate true_pred() = true; @*/

#include <assert.h>
#include <limits.h>

//@ requires true;
//@ ensures true;
void foo(int x)
{
    assert(INT_MIN <= x);
    assert(x <= INT_MAX);
}