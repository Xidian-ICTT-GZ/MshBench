#include "stdlib.h"
/*@
predicate nodes(struct node *n;) =
    n == 0 ?
        emp
    :
        n->next |-> ?next &*& n->value |-> ?value &*& malloc_block_node(n) &*& nodes(next);
@*/

/*@
predicate stack(struct stack *stack;) =
    stack->head |-> ?head &*& malloc_block_stack(stack) &*& nodes(head);
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
    stack->head = n;
    //@ close nodes(n);
    //@ close stack(stack);
}

int stack_pop(struct stack *stack)
//@ requires stack(stack) &*& stack->head |-> ?head &*& head != 0 &*& nodes(head);
//@ ensures stack(stack);
{
    //@ open nodes(head);
    struct node *head = stack->head;
    int result = head->value;
    stack->head = head->next;
    free(head);
    //@ close stack(stack);
    return result;
}

typedef bool int_predicate(int x);

struct node *nodes_filter(struct node *n, int_predicate *p)
//@ requires nodes(n);
//@ ensures nodes(result);
{
    if (n == 0)
    {
        //@ open nodes(n);
        return 0;
    }
    else
    {
        //@ open nodes(n);
        bool keep = p(n->value);
        if (keep)
        {
            struct node *next = nodes_filter(n->next, p);
            n->next = next;
            //@ close nodes(n);
            return n;
        }
        else
        {
            struct node *next = n->next;
            free(n);
            struct node *result = nodes_filter(next, p);
            return result;
        }
    }
}

void stack_filter(struct stack *stack, int_predicate *p)
//@ requires stack(stack);
//@ ensures stack(stack);
{
    //@ open stack(stack);
    struct node *head = nodes_filter(stack->head, p);
    stack->head = head;
    //@ close stack(stack);
}

void nodes_dispose(struct node *n)
//@ requires nodes(n);
//@ ensures emp;
{
    //@ open nodes(n);
    if (n != 0)
    {
        nodes_dispose(n->next);
        free(n);
    }
}

void stack_dispose(struct stack *stack)
//@ requires stack(stack);
//@ ensures emp;
{
    //@ open stack(stack);
    nodes_dispose(stack->head);
    free(stack);
}

bool neq_20(int x)
//@ requires true;
//@ ensures true;
{
    return x != 20;
}

int main()
//@ requires true;
//@ ensures true;
{
    struct stack *s = create_stack();
    stack_push(s, 10);
    stack_push(s, 20);
    stack_push(s, 30);
    stack_filter(s, neq_20);
    stack_dispose(s);
    return 0;
}