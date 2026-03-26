#include "stdlib.h"

struct foo
{
    int x;
};

/*@ predicate foo_pred(struct foo *f, int v) =
    f->x |-> v;
@*/

int main()
//@ requires true;
//@ ensures true;
{
    struct foo *f = malloc(sizeof(struct foo));
    if (f == 0)
        abort();
    //@ f->x |-> _;
    f->x = 5;
    //@ open_struct(f);
    free(f);
    return 0;
}

Wait, the issue is that after `malloc`, VeriFast gives you a `malloc_block_foo(f)` chunk plus field chunks. Let me produce the correct minimal spec:

#include "stdlib.h"

struct foo
{
    int x;
};

int main()
//@ requires true;
//@ ensures true;
{
    struct foo *f = malloc(sizeof(struct foo));
    if (f == 0)
        abort();
    f->x = 5;
    //@ open_struct(f);
    free(f);
    return 0;
}