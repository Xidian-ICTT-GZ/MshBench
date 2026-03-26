#include "stdlib.h"

/*@ predicate node(struct node *n;) =
    n != 0 &*&
    n->next |-> ?next &*&
    n->value |-> _ &*&
    (next == 0 ? true : node(next));
@*/

/*@ predicate stack(struct stack *s;) =
    s != 0 &*& s->head |-> ?head &*&
    (head == 0 ? true : node(head));
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

//@ requires true;
//@ ensures result == 0 ? true : stack(result);
struct stack *create_stack()
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
    //@ open stack_head(stack, ?head);
    struct node *oldhead = stack->head;
    n->next = oldhead;
    n->value = value;
    stack->head = n;
    //@ close node(n);
    //@ close stack(stack);
}

//@ requires stack(stack) &*& stack->head |-> 0;
//@ ensures true;
void stack_dispose(struct stack *stack)
{
    //@ open stack(stack);
    free(stack);
}

//@ requires true;
//@ ensures true;
int main()
{
    return 0;
}

Wait, let me reconsider and provide a cleaner solution:

#include "stdlib.h"

/*@ predicate node(struct node *n;) =
    n != 0 &*&
    n->next |-> ?next &*&
    n->value |-> _ &*&
    (next == 0 ? true : node(next));
@*/

/*@ predicate stack(struct stack *s;) =
    s != 0 &*& s->head |-> ?head &*&
    (head == 0 ? true : node(head));
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

//@ requires true;
//@ ensures result == 0 ? true : stack(result);
struct stack *create_stack()
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
    //@ close node(n);
    stack->head = n;
    //@ close stack(stack);
}

//@ requires stack(stack);
//@ ensures true;
void stack_dispose(struct stack *stack)
{
    //@ open stack(stack);
    free(stack);
}

//@ requires true;
//@ ensures true;
int main()
{
    return 0;
}