#include "stdlib.h"
#include "stdbool.h"

/*@
predicate stack_node(struct node *n, int value) = n->value |-> value &*& n->next |-> ?;
predicate stack_list(struct node *head) = head == 0 ? true : (exists struct node *h; h->next |-> ? &*& h->value |-> ? &*& stack_list(h->next));
predicate stack_struct(struct stack *s) = s != 0 &*& s->head |-> _ &*& stack_list(s->head);
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
//@ ensures stack_result(stack_result());
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
//@ requires stack_struct(stack);
//@ ensures stack_struct(stack);
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

int stack_pop(struct stack *stack)
//@ requires stack_struct(stack) &*& stack_list(stack->head) && exists struct node *h; h->next |-> ? &*& h->value |-> ?;
//@ ensures stack_struct(stack) &*& result == old(stack->head)->value;
{
    struct node *head = stack->head;
    int result = head->value;
    stack->head = head->next;
    free(head);
    return result;
}

typedef bool int_predicate(int x);

struct node *nodes_filter(struct node *n, int_predicate *p)
//@ requires stack_list(n);
//@ ensures stack_list(result) &*& forall struct node *x; in_list(x, result) ==> p(x->value);
{
    if (n == 0)
    {
        return 0;
    }
    else
    {
        
        bool keep = p(n->value);
        if (keep)
        {
            struct node *next = nodes_filter(n->next, p);
            
            n->next = next;
            
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
//@ requires stack_struct(stack);
//@ ensures stack_struct(stack);
{
    struct node *head = nodes_filter(stack->head, p);
    stack->head = head;
}

void nodes_dispose(struct node *n)
//@ requires stack_list(n);
//@ ensures true;
{
    if (n != 0)
    {
        nodes_dispose(n->next);
        free(n);
    }
}

void stack_dispose(struct stack *stack)
//@ requires stack_struct(stack);
//@ ensures true;
{
    nodes_dispose(stack->head);
    free(stack);
}

bool neq_20(int x) 
//@ requires true;
//@ ensures result == (x != 20);
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