#include "stdlib.h"
#include <stdbool.h>

/*@ predicate ints2(int *a, int *b; int va, int vb) =
      a != 0 &*& b != 0 &*& integer(a, va) &*& integer(b, vb);
@*/

/*@ predicate point(struct point *p; int x, int y) =
      p != 0 &*& p->x |-> x &*& p->y |-> y;
@*/

void swap(int *a, int *b)
    //@ requires ints2(a, b, ?va, ?vb);
    //@ ensures ints2(a, b, vb, va);
{
    //@ open ints2(a, b, va, vb);
    int tmp = *a;
    *a = *b;
    *b = tmp;
    //@ close ints2(a, b, vb, va);
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
    //@ close point(p, 0, 0);
    //@ open point(p, 0, 0);
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