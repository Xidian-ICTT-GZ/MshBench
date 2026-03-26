#include "stdlib.h"

struct foo
{
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
    if (f == 0)
        abort();
    //@ assume(f != 0);
    //@ assert malloc_block_foo(f);
    //@ close foo(f, _);
    f->x = 5;
    //@ open foo(f, _);

    free(f);
    return 0;
}