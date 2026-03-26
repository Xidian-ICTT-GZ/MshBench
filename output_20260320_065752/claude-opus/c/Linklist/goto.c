#include "stdlib.h"

//@ requires true;
//@ ensures true;
void foo1()
    
    
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

//@ requires true;
//@ ensures (0 <= result && (x >= 0 ? result == x : (x == INT_MIN ? false : result == -x)));
int abs(int x)
    
    
    
{
    if (0 <= x) goto end;
    if (x == INT_MIN) abort();
    x = 0 - x;
end:
    return x;
}

/*@ 
predicate nodes(struct node *n;) =
    n == 0 ? true : 
    malloc_block_node(n) &*& nodes(n->next);
@*/

struct node {
    struct node *next;
    int value;
};

//@ requires nodes(head);
//@ ensures true;
void dispose_nodes(struct node *head)
    
    
{
loop:
    //@ open nodes(head);
    if (head == 0) {
        return;
    }
    struct node *next = head->next;
    //@ close nodes(next);
    free(head);
    head = next;
    //@ open nodes(head);
    goto loop;
}

//@ requires nodes(n1) &*& nodes(n2);
//@ ensures true;
void nested_blocks(struct node *n1, struct node *n2)
    
    
{
    while (true)
        //@ invariant nodes(n1) &*& nodes(n2);
    {
        goto l1;
    l2:
        goto l3;
    l1:
        goto l2;
    }
l3:
}

//@ requires nodes(n1) &*& nodes(n2);
//@ ensures true;
void break_test(struct node *n1, struct node *n2)
    
    
{
    while (true)
        //@ invariant nodes(n1) &*& nodes(n2);
    {
        break;
    }
}