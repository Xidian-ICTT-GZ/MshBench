#include "stdlib.h"

/*@ predicate node(struct node *n; int value, struct node *next) =
    n != 0 &*&
    malloc_block_node(n) &*&
    n->value |-> value &*&
    n->next |-> next;
@*/

/*@ predicate stack(struct stack *s; list<int> values) =
    s != 0 &*&
    malloc_block_stack(s) &*&
    s->head |-> ?head &*&
    nodes(head, values);
@*/

/*@ predicate nodes(struct node *n; list<int> values) =
    switch (values) {
        case nil: return n == 0;
        case cons(h, t): return node(n, h, ?next) &*& nodes(next, t);
    };
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
    //@ close nodes(0, nil);
    //@ close stack(stack, nil);
    return stack;
}

void stack_push(struct stack *stack, int value)
//@ requires stack(stack, ?vs);
//@ ensures stack(stack, cons(value, vs));
{
    //@ open stack(stack, vs);
    struct node *n = malloc(sizeof(struct node));
    if (n == 0)
    {
        abort();
    }
    n->next = stack->head;
    n->value = value;
    //@ close node(n, value, stack->head);
    stack->head = n;
    //@ close nodes(n, cons(value, vs));
    //@ close stack(stack, cons(value, vs));
}

int stack_pop(struct stack *stack)
//@ requires stack(stack, cons(?v, ?vs));
//@ ensures stack(stack, vs) &*& result == v;
{
    //@ open stack(stack, cons(v, vs));
    struct node *head = stack->head;
    //@ open nodes(head, cons(v, vs));
    //@ open node(head, v, ?next);
    int result = head->value;
    stack->head = head->next;
    free(head);
    //@ close nodes(stack->head, vs);
    //@ close stack(stack, vs);
    return result;
}

typedef bool int_predicate(int x);

struct node *nodes_filter(struct node *n, int_predicate *p)
//@ requires nodes(n, ?vs) &*& p(?dummy) == (dummy != dummy); // dummy to bind p's type
//@ ensures nodes(result, ?ws) &*& sublist(ws, vs) == true;
{
    if (n == 0)
    {
        //@ close nodes(0, nil);
        return 0;
    }
    else
    {
        //@ open nodes(n, vs);
        //@ open node(n, ?v, ?next);
        bool keep = p(n->value);
        if (keep)
        {
            struct node *next = nodes_filter(n->next, p);
            //@ assert nodes(next, ?filtered_next);
            n->next = next;
            //@ close node(n, v, next);
            //@ close nodes(n, cons(v, filtered_next));
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
//@ requires stack(stack, ?vs) &*& p(?dummy) == (dummy != dummy);
//@ ensures stack(stack, ?ws) &*& sublist(ws, vs) == true;
{
    //@ open stack(stack, vs);
    struct node *head = nodes_filter(stack->head, p);
    //@ assert nodes(head, ?ws);
    stack->head = head;
    //@ close stack(stack, ws);
}

void nodes_dispose(struct node *n)
//@ requires nodes(n, ?vs);
//@ ensures true;
{
    if (n != 0)
    {
        //@ open nodes(n, vs);
        //@ open node(n, ?v, ?next);
        nodes_dispose(n->next);
        free(n);
    }
}

void stack_dispose(struct stack *stack)
//@ requires stack(stack, ?vs);
//@ ensures true;
{
    //@ open stack(stack, vs);
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