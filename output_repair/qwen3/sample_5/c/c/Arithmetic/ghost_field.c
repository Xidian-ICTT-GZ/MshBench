#include "stdlib.h"

struct foo
{
    int x;
};

/*@ predicate foo_pred(struct foo *f, int x) =
    f->x |-> x;
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
    //@ close foo_pred(f, 5);
    //@ open foo_pred(f, 5);
    free(f);
    return 0;
}