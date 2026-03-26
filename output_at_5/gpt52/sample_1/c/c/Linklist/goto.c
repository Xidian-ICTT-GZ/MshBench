#include "stdlib.h"

void foo1()
    //@ requires true;
    //@ ensures true;
{
    int x = 0;
    goto l1;
l3:
    assert(x == 2);
    x = 3;
    return;
l2:
    assert(x == 1);
    x = 2;
    goto l3;
l1:
    assert(x == 0);
    x = 1;
    goto l2;
}

int abs(int x)
    //@ requires true;
    //@ ensures true;
{
    if (0 <= x) goto end;
    if (x == INT_MIN) abort();
    x = 0 - x;
end:
    return x;
}

struct node {
    struct node *next;
    int value;
};

/*@
predicate node(struct node *n; struct node *next, int value) =
    n->next |-> next &*& n->value |-> value;

predicate nodes(struct node *head) =
    head == 0 ?
        true
    :
        node(head, ?next, ?value) &*& malloc_block_node(head) &*& nodes(next);
@*/

void dispose_nodes(struct node *head)
    //@ requires nodes(head);
    //@ ensures true;
{
loop:
    //@ invariant nodes(head);
    if (head == 0) return;
    //@ open nodes(head);
    //@ open node(head, ?next0, ?value0);
    struct node *next = head->next;
    free(head);
    head = next;
    //@ close nodes(head);
    goto loop;
}

void nested_blocks(struct node *n1, struct node *n2)
    //@ requires true;
    //@ ensures true;
{
    while (true)
        //@ invariant true;
    {
        goto l1;
    l2:
        goto l3;
    l1:
        goto l2;
    }
l3:
}

void break_test(struct node *n1, struct node *n2)
    //@ requires true;
    //@ ensures true;
{
    while (true)
        //@ invariant true;
    {
        break;
    }
}