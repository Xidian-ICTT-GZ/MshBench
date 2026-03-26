#include "stdlib.h"
#include <stdbool.h>

/*@ predicate point(struct point *p; int x, int y) = p->x |-> x &*& p->y |-> y; @*/

void swap(int *a, int *b)
//@ requires *a |-> ?x &*& *b |-> ?y;
//@ ensures *a |-> y &*& *b |-> x;
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
    //@ open point(p, x, y);
    swap(&p->x, &p->y);
    //@ close point(p, y, x);
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