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

/*@ predicate node(struct node *n) = n->next |-> _ &*& n->value |-> _; @*/

/*@ predicate stack(struct stack *s) = s->head |-> _; @*/

//@ ensures result != 0 &*& stack(result) &*& result->head |-> 0;
struct stack *create_stack()
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0)
    {
        abort();
    }
    stack->head = 0;

    return stack;
}

//@ requires stack(stack);
//@ ensures stack(stack);
void stack_push(struct stack *stack, int value)
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

//@ requires stack(stack);
void stack_dispose(struct stack *stack)
{
    free(stack);
}

int main()
{
    return 0;
}