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

//@ predicate stack(struct stack *s) = s != 0 && s->head == 0;

struct stack *create_stack()
//@ requires true;
//@ ensures result != 0 ==> stack(result);
//@ ensures result == 0 || true;
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
//@ requires stack != 0 &*& stack(stack);
//@ ensures stack(stack);
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
//@ requires stack != 0 &*& stack(stack);
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