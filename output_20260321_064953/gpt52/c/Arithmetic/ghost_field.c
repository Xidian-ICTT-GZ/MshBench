#include "stdlib.h"

/*@
predicate foo(struct foo *f; int x) =
    f->x |-> x;
@*/

struct foo {
    int x;
    
};

int main() 
    //@ requires true;
    //@ ensures true;
    
    
{
    struct foo *f = malloc(sizeof(struct foo));
    //@ if (f != 0) close foo(f, _);
    if (f == 0) abort();
    //@ open foo(f, _);
    f->x = 5;
    //@ close foo(f, 5);
    
    
    //@ open foo(f, _);
    free(f);
    return 0;
}