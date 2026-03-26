#include "stdlib.h"

/*@
predicate node(struct node *n; struct node *next, int value) =
    n != 0 &*& n->next |-> next &*& n->value |-> value;

predicate lseg(struct node *start, struct node *end) =
    start == end ? true : node(start, ?next, ?v) &*& lseg(next, end);

predicate stack(struct stack *s; struct node *head) =
    s != 0 &*& s->head |-> head &*& lseg(head, 0);
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
    stack->head = 0;
    //@ close stack(stack, 0);
    return stack;
}

void stack_push(struct stack *stack, int value)
    //@ requires stack(stack, ?head);
    //@ ensures stack(stack, ?newhead);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0)
    {
        abort();
    }
    //@ open stack(stack, head);
    n->next = head;
    n->value = value;
    //@ close node(n, head, value);
    stack->head = n;
    //@ close stack(stack, n);
}

int stack_pop(struct stack *stack)
    //@ requires stack(stack, ?head) &*& head != 0 &*& node(head, ?next, ?value);
    //@ ensures stack(stack, next);
{
    struct node *head = stack->head;
    //@ open stack(stack, head);
    //@ open node(head, next, value);
    int result = head->value;
    stack->head = next;
    free(head);
    //@ close stack(stack, next);
    return result;
}

typedef bool int_predicate(int x);

/*@
predicate nodes(struct node *n; ) = n == 0 ? true : node(n, ?next, ?v) &*& nodes(next);
@*/

struct node *nodes_filter(struct node *n, int_predicate *p)
    //@ requires nodes(n);
    //@ ensures nodes(result);
{
    if (n == 0)
    {
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
            //@ close node(n, next, n->value);
            //@ close nodes(n);
            return n;
        }
        else
        {
            struct node *next = n->next;
            free(n);
            struct node *result = nodes_filter(next, p);
            //@ close nodes(result);
            return result;
        }
    }
}

void stack_filter(struct stack *stack, int_predicate *p)
    //@ requires stack(stack, ?head) &*& nodes(head);
    //@ ensures stack(stack, ?newhead) &*& nodes(newhead);
{
    //@ open stack(stack, head);
    struct node *head = nodes_filter(stack->head, p);
    stack->head = head;
    //@ close stack(stack, head);
}

void nodes_dispose(struct node *n)
    //@ requires nodes(n);
    //@ ensures true;
{
    if (n != 0)
    {
        //@ open nodes(n);
        nodes_dispose(n->next);
        free(n);
    }
}

void stack_dispose(struct stack *stack)
    //@ requires stack(stack, ?head);
    //@ ensures true;
{
    //@ open stack(stack, head);
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
    //@ open stack(s, 0);
    stack_push(s, 10);
    stack_push(s, 20);
    stack_push(s, 30);
    //@ open stack(s, ?head);
    //@ close nodes(head);
    stack_filter(s, neq_20);
    //@ open stack(s, _);
    stack_dispose(s);
    return 0;
}