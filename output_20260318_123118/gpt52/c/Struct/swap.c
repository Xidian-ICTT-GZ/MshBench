#include "stdlib.h"
#include <stdbool.h>

/*@

predicate ints2(int *a, int va, int *b, int vb) =
    integer(a, va) &*& integer(b, vb);

predicate point(struct point *p, int x, int y) =
    p->x |-> x &*& p->y |-> y;

@*/

void swap(int *a, int *b)
    //@ requires ints2(a, ?va, b, ?vb);
    //@ ensures ints2(a, vb, b, va);
{
    int tmp = *a;
    *a = *b;
    *b = tmp;
}

struct point {
    int x;
    int y;
};

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
    //@ assert malloc_block_point(p);
    //@ open malloc_block_point(p);
    p->x = 3;
    p->y = 10;
    //@ close point(p, 3, 10);
    point_mirror(p);
    //@ open point(p, 10, 3);
    bool b = p->x == 10 && p->y == 3;
    assert(b);
    //@ close malloc_block_point(p);
    free(p);
    return 0;
}