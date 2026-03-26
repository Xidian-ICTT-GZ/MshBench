#include "stdlib.h"

/*@ predicate foo_ptr(struct foo *f;) = f |-> (struct foo){?x}; @*/

struct foo {
    int x;
};

int main() 
//@ requires true;
//@ ensures true;
{
    struct foo *f = malloc(sizeof(struct foo));
    if (f == 0) abort();
    //@ close foo_ptr(f);
    f->x = 5;
    //@ open foo_ptr(f);
    free(f);
    return 0;
}