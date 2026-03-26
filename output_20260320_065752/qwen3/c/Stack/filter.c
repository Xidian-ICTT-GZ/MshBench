#include "stdlib.h"

struct node
{
    struct node *next;
    int value;
};

/*@ predicate node(struct node *n; int v, struct node *next) =
    n != 0 &*& n->value |-> v &*& n->next |-> next;
@*/

/*@ predicate nodes(struct node *n; list<int> vs) =
    n == 0 ? vs == nil : 
    exists<int> v &*& exists<struct node*> next &*&
    node(n, v, next) &*& nodes(next, ?vs1) &*& vs == cons(v, vs1);
@*/

/*@ predicate stack(struct stack *s; list<int> vs) =
    s != 0 &*& s->head |-> ?head &*& nodes(head, vs);
@*/

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
    //@ open nodes(stack->head, vs);
    struct node *n = malloc(sizeof(struct node));
    if (n == 0)
    {
        abort();
    }
    n->next = stack->head;
    n->value = value;
    //@ close node(n, value, stack->head);
    //@ close nodes(n, cons(value, vs));
    stack->head = n;
    //@ close stack(stack, cons(value, vs));
}

int stack_pop(struct stack *stack)
//@ requires stack(stack, cons(?v, ?vs));
//@ ensures stack(stack, vs) &*& result == v;
{
    //@ open stack(stack, cons(v, vs));
    //@ open nodes(stack->head, cons(v, vs));
    struct node *head = stack->head;
    int result = head->value;
    stack->head = head->next;
    free(head);
    //@ close stack(stack, vs);
    return result;
}

typedef bool int_predicate(int x);

struct node *nodes_filter(struct node *n, int_predicate *p)
//@ requires nodes(n, ?vs) &*& p(?x) == (x != 20); // specific to neq_20 used in main
//@ ensures nodes(result, ?filtered_vs) &*& filtered_vs == filter_neq_20(vs);
{
    if (n == 0)
    {
        //@ close nodes(0, nil);
        return 0;
    }
    else
    {
        //@ open nodes(n, vs);
        //@ assert node(n, ?v, ?next);
        bool keep = p(n->value);
        if (keep)
        {
            struct node *next = nodes_filter(n->next, p);
            //@ open nodes(n->next, ?vs1);
            //@ close nodes(n, cons(v, ?filtered_vs1));
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

/*@ lemma list<int> filter_neq_20(list<int> xs)
    requires true;
    ensures true;
{
    switch(xs) {
        case nil: return;
        case cons(h, t):
            filter_neq_20(t);
            return;
    }
}
@*/

void stack_filter(struct stack *stack, int_predicate *p)
//@ requires stack(stack, ?vs) &*& p(?x) == (x != 20);
//@ ensures stack(stack, filter_neq_20(vs));
{
    //@ open stack(stack, vs);
    struct node *head = nodes_filter(stack->head, p);
    stack->head = head;
    //@ close stack(stack, filter_neq_20(vs));
}

void nodes_dispose(struct node *n)
//@ requires nodes(n, ?vs);
//@ ensures true;
{
    if (n != 0)
    {
        //@ open nodes(n, vs);
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