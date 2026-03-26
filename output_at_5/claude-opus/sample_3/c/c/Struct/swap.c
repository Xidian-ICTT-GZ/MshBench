#include "stdlib.h"
#include <stdbool.h>

/*@
predicate int_cell(int *p; int v) = pointer(p, _) &*& p |-> v;
@*/

void swap(int *a, int *b)
  //@ requires a |-> ?va &*& b |-> ?vb;
  //@ ensures a |-> vb &*& b |-> va;
{
    int tmp = *a;
    *a = *b;
    *b = tmp;
}

/*@
predicate point_pred(struct point *p; int x, int y) =
    p->x |-> x &*& p->y |-> y;
@*/

struct point {
    int x;
    int y;
};

void point_mirror(struct point *p)
  //@ requires point_pred(p, ?x, ?y);
  //@ ensures point_pred(p, y, x);
{
    swap(&p->x, &p->y);
}

int main() 
  //@ requires true;
  //@ ensures true;
{
    struct point *p = malloc(sizeof(struct point));
    if (p == 0) { abort(); }
    //@ close point_pred(p, 0, 0);
    p->x = 3;
    p->y = 10;
    //@ open point_pred(p, 0, 0);
    //@ close point_pred(p, 3, 10);
    point_mirror(p);
    bool b = p->x == 10 && p->y == 3;
    assert(b);
    //@ open point_pred(p, _, _);
    free(p);
    return 0;
}