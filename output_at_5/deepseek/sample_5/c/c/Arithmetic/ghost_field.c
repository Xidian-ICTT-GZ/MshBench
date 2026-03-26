#include "stdlib.h"

struct foo {
    int x;
    
};

/*@
predicate foo(struct foo *f) =
    malloc_block_foo(f) &*& struct_foo_padding(f) &*& f->x |-> _;
@*/

int main() 
    //@ requires true;
    //@ ensures true;
    
{
    struct foo *f = malloc(sizeof(struct foo));
    if (f == 0) abort();
    //@ close malloc_block_foo(f);
    //@ close struct_foo_padding(f);
    //@ close foo(f);
    f->x = 5;
    //@ open foo(f);
    //@ open struct_foo_padding(f);
    
    free(f);
    return 0;
}