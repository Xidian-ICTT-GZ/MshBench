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
predicate nodes(struct node *node, int count) =
    node == 0 ?
        count == 0
    :
        node->next |-> ?next &*& node->value |-> ?value &*&
        malloc_block_node(node) &*&
        nodes(next, ?count0) &*& count == count0 + 1;

predicate stack(struct stack *stack, int count) =
    stack->head |-> ?head &*&
    malloc_block_stack(stack) &*&
    nodes(head, count);
@*/

struct stack *create_stack()
//@ requires true;
//@ ensures stack(result, 0);
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0)
    {
        abort();
    }
    stack->head = 0;
    //@ close nodes(0, 0);
    //@ close stack(stack, 0);
    return stack;
}

void stack_push(struct stack *stack, int value)
//@ requires stack(stack, ?count);
//@ ensures stack(stack, count + 1);
{
    //@ open stack(stack, count);
    struct node *n = malloc(sizeof(struct node));
    if (n == 0)
    {
        abort();
    }
    n->next = stack->head;
    n->value = value;
    //@ close nodes(n, count + 1);
    stack->head = n;
    //@ close stack(stack, count + 1);
}

void stack_dispose(struct stack *stack)
//@ requires stack(stack, 0);
//@ ensures true;
{
    //@ open stack(stack, 0);
    //@ open nodes(_, 0);
    free(stack);
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}