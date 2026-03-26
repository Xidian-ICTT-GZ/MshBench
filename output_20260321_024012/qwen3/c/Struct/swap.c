#include "stdlib.h"
#include <stdbool.h>

/*@
predicate swap_space(int *a, int *b; int old_a, int old_b) =
    a != b &*&
    *a |-> old_a &*& *b |-> old_b;
@*/

void swap(int *a, int *b)
//@ requires swap_space(a, b, ?old_a, ?old_b);
//@ ensures swap_space(a, b, old_b, old_a);
{
    int tmp = *a;
    *a = *b;
    *b = tmp;
}

struct point {
    int x;
    int y;
};

/*@
predicate point(struct point *p; int x, int y) =
    p->x |-> x &*& p->y |-> y;
@*/

void point_mirror(struct point *p)
//@ requires point(p, ?x, ?y);
//@ ensures point(p, y, x);
{
    swap(&p->x, &p->y);
}

int main() 
//@ requires true;
//@ ensures true;
{
    struct point *p = malloc(sizeof(struct point));
    if (p == 0) { abort(); }
    //@ close point(p, 3, 10);
    p->x = 3;
    p->y = 10;
    point_mirror(p);
    bool b = p->x == 10 && p->y == 3;
    //@ open point(p, _, _);
    assert(b);
    free(p);
    return 0;
}