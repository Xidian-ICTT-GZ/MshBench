#include "stdlib.h"

/*@
predicate foo(struct foo *f;) = malloc_block_foo(f) &*& f->x |-> _;
@*/

struct foo {
    int x;
    
};

/*@
lemma void malloc_block_foo_close(struct foo *f)
    requires malloc_block(f, sizeof(struct foo));
    ensures  foo(f);
{
    close foo(f);
}

lemma void malloc_block_foo_open(struct foo *f)
    requires foo(f);
    ensures  malloc_block(f, sizeof(struct foo));
{
    open foo(f);
}
@*/

int main() 
    
    
//@ requires true;
//@ ensures true;
{
    struct foo *f = malloc(sizeof(struct foo));
    if (f == 0) abort();
    //@ malloc_block_foo_close(f);
    f->x = 5;
    //@ malloc_block_foo_open(f);
    free(f);
    return 0;
}