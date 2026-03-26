#include "stdlib.h"

struct foo {
    int x;
    
};

/*@ predicate foo(struct foo *f; int x) =
        f->x |-> x;
@*/

int main() 
    //@ requires true;
    //@ ensures true;
    
    
{
    struct foo *f = malloc(sizeof(struct foo));
    if (f == 0) abort();
    //@ assume(f != 0);
    //@ close foo(f, _);
    //@ open foo(f, _);
    f->x = 5;
    //@ close foo(f, 5);
    
    
    //@ open foo(f, _);
    free(f);
    return 0;
}