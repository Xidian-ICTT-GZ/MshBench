#include "stdlib.h"

/*@

predicate node(struct node *n; list<int> vals) =
    n != 0 &*& n->value |-> ?v &*& n->next |-> ?nx &*& node(nx, ?rest) &*&
    vals == cons(v, rest)
  || n == 0 &*& vals == nil;

predicate stack(struct stack *s; list<int> vals) =
    s != 0 &*& s->head |-> ?h &*& node(h, vals);

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

    return stack;
}

void stack_push(struct stack *stack, int value)
    //@ requires stack(stack, ?vals);
    //@ ensures stack(stack, cons(value, vals));
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0)
    {
        abort();
    }
    n->next = stack->head;
    n->value = value;
    stack->head = n;
}

void stack_dispose(struct stack *stack)
    //@ requires stack(stack, nil);
    //@ ensures true;
{
    free(stack);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    return 0;
}