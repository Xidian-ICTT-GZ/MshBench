#include "stdlib.h"
#include <stdbool.h>

//@ predicate point(struct point *p) = p->x |-> _ &*& p->y |-> _;

void swap(int *a, int *b)
//@ requires *a |-> ?va &*& *b |-> ?vb;
//@ ensures *a |-> vb &*& *b |-> va;
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

void point_mirror(struct point *p)
//@ requires p->x |-> ?vx &*& p->y |-> ?vy;
//@ ensures p->x |-> vy &*& p->y |-> vx;
{
    swap(&p->x, &p->y);
}

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
    point_mirror(p);
    bool b = p->x == 10 && p->y == 3;
    assert(b);
    free(p);
    return 0;
}