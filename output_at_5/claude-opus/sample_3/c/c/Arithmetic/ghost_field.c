#include "stdlib.h"

/*@
predicate foo(struct foo *f) = f->x |-> _;
@*/

struct foo {
    int x;
    
};

int main() 
    
    
//@ requires true;
//@ ensures true;
{
    struct foo *f = malloc(sizeof(struct foo));
    if (f == 0) abort();
    //@ close foo(f);
    f->x = 5;
    //@ open foo(f);
    
    free(f);
    return 0;
}