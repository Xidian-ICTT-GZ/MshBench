#include "stdlib.h"

struct node
{
    struct node *next;
    int value;
};

struct stack
{
    struct node *head;
};

/*@
predicate nodes(struct node *n) =
    n == 0 ?
        true
    :
        n->next |-> ?next &*& n->value |-> _ &*& malloc_block_node(n) &*& nodes(next);

predicate stackp(struct stack *s) =
    s->head |-> ?h &*& malloc_block_stack(s) &*& nodes(h);
@*/

struct stack *create_stack()
//@ requires true;
//@ ensures stackp(result);
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0)
    {
        abort();
    }
    stack->head = 0;
    
    //@ close nodes(0);
    //@ close stackp(stack);
    return stack;
}

void stack_push(struct stack *stack, int value)
//@ requires stackp(stack);
//@ ensures stackp(stack);
{
    //@ open stackp(stack);
    struct node *n = malloc(sizeof(struct node));
    if (n == 0)
    {
        abort();
    }
    n->next = stack->head;
    n->value = value;
    stack->head = n;
    
    //@ close nodes(n);
    //@ close stackp(stack);
}

void stack_dispose(struct stack *stack)
//@ requires stackp(stack);
//@ ensures true;
{
    //@ open stackp(stack);
    //@ open nodes(?h);
    //@ leak nodes(h);
    free(stack);
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}