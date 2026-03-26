#include "stdlib.h"

/*@
predicate nodes(struct node *head) =
    head == 0 ? emp : head->next |-> ?next &*& head->value |-> _ &*& malloc_block(head) &*& nodes(next);
@*/

//@ requires true;
//@ ensures true;
void foo1()
{
    int x = 0;
    //@ assert x == 0;
    goto l1;
l3:
    //@ assert x == 2;
    assert(x == 2);
    x = 3;
    return;
l2:
    //@ assert x == 1;
    assert(x == 1);
    x = 2;
    goto l3;
l1:
    //@ assert x == 0;
    assert(x == 0);
    x = 1;
    goto l2;
}

//@ requires true;
//@ ensures true;
int abs(int x)
{
    if (0 <= x) goto end;
    if (x == INT_MIN) abort();
    x = 0 - x;
end:
    return x;
}

//@ requires nodes(head);
//@ ensures emp;
void dispose_nodes(struct node *head)
{
loop:
    //@ open nodes(head);
    if (head == 0) {
        //@ close nodes(head);
        return;
    }
    struct node *next = head->next;
    free(head);
    head = next;
    goto loop;
}

//@ requires true;
//@ ensures true;
void nested_blocks(struct node *n1, struct node *n2)
{
    while (true)
    {
        goto l1;
    l2:
        goto l3;
    l1:
        goto l2;
    }
l3:
}

//@ requires true;
//@ ensures true;
void break_test(struct node *n1, struct node *n2)
{
    while (true)
    {
        break;
    }
}