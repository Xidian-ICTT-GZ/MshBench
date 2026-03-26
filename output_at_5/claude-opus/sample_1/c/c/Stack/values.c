#include "stdlib.h"

/*@
predicate node(struct node *n;) =
    n != 0 &*& n->next |-> ?next &*& n->value |-> _ &*& (next == 0 ? true : node(next));
predicate stack(struct stack *s;) = s != 0 &*& s->head |-> ?head &*& (head == 0 ? true : node(head));
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
    //@ requires emp;
    //@ ensures stack(result);
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0)
    {
        abort();
    }
    stack->head = 0;
    
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
    //@ close node(n);
    //@ close stack(stack);
}

void stack_dispose(struct stack *stack)
    //@ requires stack(stack);
    //@ ensures emp;
{
    //@ open stack(stack);
    //@ close emp;
    free(stack);
}

int main()
    //@ requires emp;
    //@ ensures emp;
{
    return 0;
}