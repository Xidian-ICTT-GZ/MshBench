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
    n == 0 ? true : n->next |-> ?next &*& n->value |-> ?v &*& malloc_block_node(n) &*& nodes(next);
predicate stack(struct stack *s) =
    s->head |-> ?head &*& malloc_block_stack(s) &*& nodes(head);
@*/

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
    //@ close nodes(n);
    stack->head = n;
    //@ close stack(stack);
}

void stack_dispose(struct stack *stack)
//@ requires stack(stack);
//@ ensures true;
{
    //@ open stack(stack);
    //@ struct node *head = stack->head;
    //@ open nodes(head);
    //@ if (head != 0) { open nodes(head->next); }
    free(stack);
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}