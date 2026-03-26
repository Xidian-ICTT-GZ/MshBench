#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};

/*@ predicate nodes(struct node *n) =
    n == 0 ?
        emp
    :
        n->next |-> ?next &*& n->value |-> _ &*& malloc_block_node(n) &*& nodes(next);
@*/

void foo1()
    
//@ requires true;
//@ ensures true;
{
    int x = 0;
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

int abs(int x)
    
//@ requires true;
//@ ensures 0 <= result;
//@ ensures (x >= 0 ==> result == x) &*& (x < 0 &*& x != INT_MIN ==> result == 0 - x);
{
    if (0 <= x) goto end;
    if (x == INT_MIN) abort();
    x = 0 - x;
end:
    return x;
}

void dispose_nodes(struct node *head)
    
//@ requires nodes(head);
//@ ensures emp;
{
loop:
    if (head == 0) return;
    else {
        struct node *next = head->next;
        //@ open nodes(head);
        free(head);
        head = next;
        goto loop;
    }
}

void nested_blocks(struct node *n1, struct node *n2)
    
//@ requires nodes(n1) &*& nodes(n2);
//@ ensures nodes(n1) &*& nodes(n2);
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
    
//@ requires nodes(n1) &*& nodes(n2);
//@ ensures nodes(n1) &*& nodes(n2);
{
    while (true)

    {
        break;
    }
}