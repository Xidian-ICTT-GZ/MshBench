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
        n->next |-> ?next &*& n->value |-> ?v &*& malloc_block_node(n) &*& nodes(next);

predicate stack_pred(struct stack *s) =
    s->head |-> ?h &*& malloc_block_stack(s) &*& nodes(h);

@*/

struct stack *create_stack()
    //@ requires true;
    //@ ensures stack_pred(result);
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0)
    {
        abort();
    }
    stack->head = 0;
    //@ close nodes(0);
    //@ close stack_pred(stack);
    
    return stack;
}

void stack_push(struct stack *stack, int value)
    //@ requires stack_pred(stack);
    //@ ensures stack_pred(stack);
{
    //@ open stack_pred(stack);
    struct node *n = malloc(sizeof(struct node));
    if (n == 0)
    {
        abort();
    }
    n->next = stack->head;
    n->value = value;
    //@ close nodes(n);
    stack->head = n;
    //@ close stack_pred(stack);
    
    
}

void stack_dispose(struct stack *stack)
    //@ requires stack_pred(stack);
    //@ ensures true;
{
    //@ open stack_pred(stack);
    //@ open nodes(stack->head);
    free(stack);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    return 0;
}