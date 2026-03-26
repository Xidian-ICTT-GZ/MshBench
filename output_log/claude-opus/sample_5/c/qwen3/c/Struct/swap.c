#include "stdlib.h"
#include <stdbool.h>

/*@
predicate point(struct point *p; int x, int y) =
    p != 0 &*&
    p->x |-> x &*&
    p->y |-> y &*&
    malloc_block_point(p);
@*/

struct point
{
    int x;
    int y;
};

/*@
requires a != b &*& integer(a, ?va) &*& integer(b, ?vb);
ensures integer(a, vb) &*& integer(b, va);
@*/
void swap(int *a, int *b)
{
    int tmp = *a;
    *a = *b;
    *b = tmp;
}

/*@
requires point(p, ?x, ?y);
ensures point(p, y, x);
@*/
void point_mirror(struct point *p)
//@ open point(p, _, _);
{
    swap(&p->x, &p->y);
}
//@ close point(p, _, _);

int main()
//@ requires true;
//@ ensures true;
{
    struct point *p = malloc(sizeof(struct point));
    if (p == 0)
    {
        abort();
    }
    p->x = 3;
    p->y = 10;
    //@ close point(p, 3, 10);
    point_mirror(p);
    //@ open point(p, 10, 3);
    bool b = p->x == 10 && p->y == 3;
    assert(b);
    //@ close point(p, 10, 3);
    //@ open point(p, 10, 3);
    free(p);
    return 0;
}