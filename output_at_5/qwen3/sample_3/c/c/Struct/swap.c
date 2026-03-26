#include "stdlib.h"
#include <stdbool.h>

//@ predicate point(struct point *p) = p->x |-> int &*& p->y |-> int;

void swap(int *a, int *b)
//@ requires a != b &*& true;
//@ ensures true;
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
//@ requires point(p);
//@ ensures point(p);
{
    swap(&p->x, &p->y);
}

int main() 
//@ requires true;
//@ ensures true;
{
    struct point *p = malloc(sizeof(struct point));
    if (p == 0) { abort(); }
    //@ open point(p);
    p->x = 3;
    p->y = 10;
    point_mirror(p);
    bool b = p->x == 10 && p->y == 3;
    assert(b);
    free(p);
    return 0;
}