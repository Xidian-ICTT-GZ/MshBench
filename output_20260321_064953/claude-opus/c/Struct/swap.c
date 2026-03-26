#include "stdlib.h"
#include <stdbool.h>

/*@
predicate int_ptr(int *p; int v) = pointer(p, ?perm) &*& perm >= 1 &*& *p |-> v;
@*/

void swap(int *a, int *b)
    //@ requires int_ptr(a; ?va) &*& int_ptr(b; ?vb);
    //@ ensures int_ptr(a; vb) &*& int_ptr(b; va);
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
predicate point_pred(struct point *p; int x, int y) =
    p->x |-> x &*& p->y |-> y;
@*/

void point_mirror(struct point *p)
    //@ requires point_pred(p; ?x, ?y);
    //@ ensures point_pred(p; y, x);
{
    swap(&p->x, &p->y);
}

int main() 
    //@ requires true;
    //@ ensures true;
{
    struct point *p = malloc(sizeof(struct point));
    if (p == 0) { abort(); }
    //@ close point_pred(p; _, _);
    p->x = 3;
    p->y = 10;
    //@ open point_pred(p; _, _);
    point_mirror(p);
    //@ open point_pred(p; ?a, ?b);
    bool b = p->x == 10 && p->y == 3;
    assert(b);
    //@ close point_pred(p; p->x, p->y);
    free(p);
    return 0;
}