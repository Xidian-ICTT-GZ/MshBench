#include "stdlib.h"

/*@ predicate stack(struct stack *s; list<int> values) =
    s != 0 &*&
    malloc_block_stack(s) &*&
    nodes(s->head, values);
@*/

/*@ predicate nodes(struct node *n; list<int> values) =
    n == 0 ? values == nil :
    n->next |-> ?next &*& n->value |-> ?value &*&
    malloc_block_node(n) &*&
    nodes(next, ?rest) &*& values == cons(value, rest);
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
//@ ensures stack(result, nil);
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0)
    {
        abort();
    }
    stack->head = 0;
    //@ close nodes(0, nil);
    //@ close stack(stack, nil);
    return stack;
}

void stack_push(struct stack *stack, int value)
//@ requires stack(stack, ?old_values);
//@ ensures stack(stack, cons(value, old_values));
{
    //@ open stack(stack, old_values);
    struct node *n = malloc(sizeof(struct node));
    if (n == 0)
    {
        abort();
    }
    n->next = stack->head;
    n->value = value;
    stack->head = n;
    //@ close nodes(n, cons(value, old_values));
    //@ close stack(stack, cons(value, old_values));
}

void stack_dispose(struct stack *stack)
//@ requires stack(stack, ?values);
//@ ensures true;
{
    //@ open stack(stack, values);
    free(stack);
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}