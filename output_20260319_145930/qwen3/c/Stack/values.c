#include "stdlib.h"

/*@ predicate stack(struct stack *s; list<int> values) =
    s != 0 &*&
    malloc_block_stack(s) &*&
    nodes(s->head, values);
@*/

/*@ predicate nodes(struct node *node; list<int> values) =
    node == 0 ?
        values == nil
    :
        malloc_block_node(node) &*&
        nodes(node->next, ?rest) &*&
        values == cons(node->value, rest);
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
    //@ open nodes(stack->head, values);
    free(stack);
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}