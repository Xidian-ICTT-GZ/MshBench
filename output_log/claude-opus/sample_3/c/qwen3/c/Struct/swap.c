#include "stdlib.h"
#include <stdbool.h>

/*@ predicate pointer_to_int(int *p; int v) = p::int(v); @*/

/*@ predicate swap_pre(int *a, int *b) =
    a != b &*&
    malloc_block_int(a, _) &*&
    malloc_block_int(b, _) &*&
    pointer_to_int(a, ?va) &*&
    pointer_to_int(b, ?vb);
@*/

/*@ predicate swap_post(int *a, int *b, int va, int vb) =
    a != b &*&
    malloc_block_int(a, _) &*&
    malloc_block_int(b, _) &*&
    pointer_to_int(a, vb) &*&
    pointer_to_int(b, va);
@*/

/*@ requires swap_pre(a, b);
    ensures swap_post(a, b, ?va, ?vb);
@*/
void swap(int *a, int *b)
{
    int tmp = *a;
    *a = *b;
    *b = tmp;
}

struct point
{
    int x;
    int y;
};

/*@ predicate point(struct point *p; int x, int y) =
    p != 0 &*&
    malloc_block_point(p, sizeof(struct point)) &*&
    pointer_to_int(&p->x, x) &*&
    pointer_to_int(&p->y, y);
@*/

/*@ requires point(p, ?x, ?y);
    ensures point(p, y, x);
@*/
void point_mirror(struct point *p)
{
    //@ open point(p, x, y);
    //@ assert pointer_to_int(&p->x, x);
    //@ assert pointer_to_int(&p->y, y);
    swap(&p->x, &p->y);
    //@ close point(p, y, x);
}

int main()
{
    struct point *p = malloc(sizeof(struct point));
    if (p == 0)
    {
        abort();
    }
    //@ close point(p, 3, 10);
    p->x = 3;
    p->y = 10;
    //@ assert point(p, 3, 10);
    point_mirror(p);
    //@ assert point(p, 10, 3);
    bool b = p->x == 10 && p->y == 3;
    assert(b);
    free(p);
    return 0;
}