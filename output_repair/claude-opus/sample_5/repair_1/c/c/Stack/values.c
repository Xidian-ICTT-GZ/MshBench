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

/*@ predicate nodes(struct node *n;) =
    n == 0 ? emp : n->next |-> ?next &*& n->value |-> _ &*& malloc_block_node(n) &*& nodes(next);
@*/

/*@ predicate stack(struct stack *s;) =
    s->head |-> ?head &*& malloc_block_stack(s) &*& nodes(head);
@*/

//@ requires true;
//@ ensures stack(result);
struct stack *create_stack()
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

//@ requires stack(stack);
//@ ensures stack(stack);
void stack_push(struct stack *stack, int value)
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

//@ requires stack(stack) &*& stack->head |-> 0;
//@ ensures true;
void stack_dispose(struct stack *stack)
{
    //@ open stack(stack);
    //@ open nodes(0);
    free(stack);
}

//@ requires true;
//@ ensures true;
int main()
{
    return 0;
}