#include "stdlib.h"
#include <stdbool.h>

/*@ predicate int_ptr(int *p; int v) = p |-> v; @*/

/*@ requires int_ptr(a, ?va) &*& int_ptr(b, ?vb);
    ensures int_ptr(a, vb) &*& int_ptr(b, va);
*/
void swap(int *a, int *b)
{
    int tmp = *a;
    *a = *b;
    *b = tmp;
}

struct point {
    int x;
    int y;
};

/*@ predicate point(struct point *p; int x, int y) = 
      p->x |-> x &*& p->y |-> y; @*/

/*@ requires point(p, ?x, ?y);
    ensures point(p, y, x);
*/
void point_mirror(struct point *p)
{
    //@ open point(p, _, _);
    swap(&p->x, &p->y);
    //@ close point(p, p->x, p->y);
}

int main() 
/*@ requires true;
    ensures true;
*/
{
    struct point *p = malloc(sizeof(struct point));
    if (p == 0) { abort(); }
    //@ close point(p, 3, 10);
    p->x = 3;
    p->y = 10;
    point_mirror(p);
    //@ open point(p, ?x, ?y);
    bool b = p->x == 10 && p->y == 3;
    assert(b);
    //@ open point(p, _, _);
    free(p);
    return 0;
}