#include "stdlib.h"

struct node { 
    int value; 
    struct node *next; 
};

/*@ predicate node(struct node *p; int v, struct node *q) =
    p != 0 &*& p->value |-> v &*& p->next |-> q;
@*/

/*@ predicate list(struct node *head; list<int> vs) =
    head == 0 &*& vs == nil
    || (
        head != 0
        &*& node(head; ?v, ?tail)
        &*& list(tail; ?tail_vs)
        &*& vs == cons(v, tail_vs)
    );
@*/

void foo1()
{
    int x = 0;
    goto l1;
l3:
    //@ assert x == 2;
    x = 3;
    return;
l2:
    //@ assert x == 1;
    x = 2;
    goto l3;
l1:
    //@ assert x == 0;
    x = 1;
    goto l2;
}

int abs(int x)
{
    //@ requires true;
    //@ ensures result >= 0 &*& (x >= 0 ==> result == x) &*& (x < 0 ==> result == -x);
    if (0 <= x) goto end;
    if (x == INT_MIN) abort();
    x = 0 - x;
end:
    return x;
}

void dispose_nodes(struct node *head)
    //@ requires list(head, ?vs);
    //@ ensures true;
{
loop:
    if (head == 0) return;
    //@ open list(head, vs);
    //@ open node(head, ?v, ?next);
    struct node* next = head->next;
    free(head);
    head = next;
    //@ close list(head, ?rest_vs);
    goto loop;
}

void nested_blocks(struct node *n1, struct node *n2)
    //@ requires true;
    //@ ensures true;
{
    while (true)
        //@ invariant true; // no meaningful loop invariant possible without state change
    {
        goto l1;
    l2:
        goto l3;
    l1:
        goto l2;
    }
l3:
    ;
}

void break_test(struct node *n1, struct node *n2)
    //@ requires true;
    //@ ensures true;
{
    while (true)
        //@ invariant true; // no meaningful loop invariant possible since loop breaks immediately
    {
        break;
    }
}