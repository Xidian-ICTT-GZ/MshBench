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
predicate list_node(struct node *head, int val) =
    head != null &*& head->value == val &*& head->next == null;

predicate list_nodes(struct node *head) =
    head == null ||
    (head->value == ? && head->next != null && list_nodes(head->next));
@*/

void dispose_nodes(struct node *head)
//@ requires list_nodes(head);
//@ ensures true;
{
loop:
    //@ invariant list_nodes(head);
    if (head == 0) return;
    struct node *next = head->next;
    free(head);
    head = next;
    goto loop;
}

void nested_blocks(struct node *n1, struct node *n2)
//@ requires true;
//@ ensures true;
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

void break_test(struct node *n1, struct node *n2)
//@ requires true;
//@ ensures true;
{
    while (true)
    {
        break;
    }
}