#include <limits.h>
#include <stdlib.h>
/*@
predicate integer(int *p) = integer(p, _);
predicate integer(int *p; int v) = p != 0 &*& *p == v &*& malloc_block_int(p);
@*/

void foo(int x)
//@ requires true;
//@ ensures true;
{
    //@ close integer(&x, x);
    //@ open integer(&x, x);
    assert(INT_MIN <= x);
    assert(x <= INT_MAX);
}