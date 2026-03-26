#include "stdlib.h"

struct foo {
    int x;
    
};

/*@
predicate foo(struct foo *f; int x) =
    f->x |-> x &*& malloc_block_foo(f);
@*/

int main() 
    //@ requires true;
    //@ ensures true;
    
    
{
    struct foo *f = malloc(sizeof(struct foo));
    if (f == 0) abort();
    //@ close foo(f, _);
    //@ open foo(f, _);
    f->x = 5;
    
    
    //@ close foo(f, 5);
    //@ open foo(f, 5);
    free(f);
    return 0;
}