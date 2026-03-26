#include "stdlib.h"

/*@
predicate nodes(struct node *node;) =
    node == 0 ?
        emp
    :
        node->next |-> ?next &*& node->value |-> ?value &*& malloc_block_node(node) &*& nodes(next);

predicate stack(struct stack *stack;) =
    stack->head |-> ?head &*& malloc_block_stack(stack) &*& nodes(head);
@*/

struct node
{
    struct node *next;
    int value;
};

struct stack
{
    struct node *head;
};

struct stack *create_stack()
//@ requires true;
//@ ensures stack(result);
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0)
    {
        abort();
    }
    stack->head = 0;
    //@ close nodes(0);
    //@ close stack(stack);
    return stack;
}

void stack_push(struct stack *stack, int value)
//@ requires stack(stack);
//@ ensures stack(stack);
{
    //@ open stack(stack);
    struct node *n = malloc(sizeof(struct node));
    if (n == 0)
    {
        abort();
    }
    n->next = stack->head;
    n->value = value;
    stack->head = n;
    //@ close nodes(n);
    //@ close stack(stack);
}

void stack_dispose(struct stack *stack)
//@ requires stack(stack);
//@ ensures true;
{
    //@ open stack(stack);
    //@ open nodes(stack->head);
    free(stack);
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}