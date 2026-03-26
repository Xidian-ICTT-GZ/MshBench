#include "stdlib.h"

/*@ predicate node(struct node *n) =
    n != 0 &*&
    n->next |-> ?next &*&
    n->value |-> ?val &*&
    (next == 0 ? true : node(next));
@*/

/*@ predicate stack(struct stack *s; struct node *head) =
    s != 0 &*& s->head |-> head &*&
    (head == 0 || node(head));
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
    //@ ensures stack(result, 0);
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0)
    {
        abort();
    }
    //@ assume stack != 0;
    //@ split_malloc(sizeof(struct stack));
    stack->head = 0;
    //@ close stack(stack, 0);
    return stack;
}

void stack_push(struct stack *stack, int value)
    //@ requires stack(stack, ?head);
    //@ ensures stack(stack, ?new_head);
{
    //@ open stack(stack, head);
    struct node *n = malloc(sizeof(struct node));
    if (n == 0)
    {
        abort();
    }
    //@ assume n != 0;
    //@ split_malloc(sizeof(struct node));
    n->next = stack->head;
    n->value = value;
    stack->head = n;
    //@ close node(n);
    //@ close stack(stack, n);
}

void stack_dispose(struct stack *stack)
    //@ requires stack(stack, ?head);
    //@ ensures true;
{
    //@ open stack(stack, head);
    free(stack);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    return 0;
}