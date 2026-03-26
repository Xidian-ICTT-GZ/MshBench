#include "stdlib.h"

struct foo
{
    int x;
};

/*@ predicate foo(struct foo *p; int x) =
    p != 0 &*& p->x |-> x;
@*/

int main()
{
    struct foo *f = malloc(sizeof(struct foo));
    if (f == 0)
        abort();
    //@ requires true;
    //@ ensures foo(f, 5);
    f->x = 5;

    //@ requires foo(f, 5);
    //@ ensures true;
    free(f);
    return 0;
}