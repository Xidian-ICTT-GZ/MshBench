#include "stdlib.h"

/*@
predicate node(struct node *n;) =
    n->next |-> ?next &*& n->value |-> ?value &*& malloc_block_node(n);
@*/

void foo1()
    //@ requires true;
    //@ ensures true;
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

void dispose_nodes(struct node *head)
    //@ requires node(head);
    //@ ensures true;
{
loop:
    //@ open node(head);
    if (head == 0) return;
    struct node *next = head->next;
    free(head);
    head = next;
    goto loop;
}

void nested_blocks(struct node *n1, struct node *n2)
    //@ requires node(n1) &*& node(n2);
    //@ ensures node(n1) &*& node(n2);
{
    while (true)
        //@ invariant node(n1) &*& node(n2);
    {
        goto l1;
    l2:
        goto l3;
    l1:
        goto l2;
    }
l3:
    //@ close node(n1);
    //@ close node(n2);
}

void break_test(struct node *n1, struct node *n2)
    //@ requires node(n1) &*& node(n2);
    //@ ensures node(n1) &*& node(n2);
{
    while (true)
        //@ invariant node(n1) &*& node(n2);
    {
        break;
    }
}