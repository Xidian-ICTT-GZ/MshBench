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
    //@ assert true;
    f->x = 5;

    //@ open true;
    //@ close foo(f, 5);
    //@ assert foo(f, 5);

    //@ open foo(f, 5);
    free(f);
    return 0;
}