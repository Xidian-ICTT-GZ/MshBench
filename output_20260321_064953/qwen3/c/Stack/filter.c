#include "stdlib.h"

/*@ 
predicate node(struct node *n; int value, struct node *next) =
    n != 0 &*&
    malloc_block_node(n) &*&
    n->value |-> value &*&
    n->next |-> next;
@*/

/*@ 
predicate stack(struct stack *s; list<int> values) =
    s != 0 &*&
    malloc_block_stack(s) &*&
    s->head |-> ?head &*&
    nodes(head, values);
@*/

/*@ 
predicate nodes(struct node *n; list<int> values) =
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
    
    
    return stack;
}

void stack_push(struct stack *stack, int value)

//@ requires stack(stack, ?vs);
//@ ensures stack(stack, cons(value, vs));
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

//@ requires stack(stack, cons(?v, ?vs));
//@ ensures stack(stack, vs) &*& result == v;
{
    
    struct node *head = stack->head;
    
    int result = head->value;
    stack->head = head->next;
    free(head);
    
    return result;
}

typedef bool int_predicate(int x);

struct node *nodes_filter(struct node *n, int_predicate *p)

//@ requires nodes(n, ?vs) &*& ints_forall(vs, p);
//@ ensures nodes(result, filter(p, vs));
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

//@ requires stack(stack, ?vs) &*& ints_forall(vs, p);
//@ ensures stack(stack, filter(p, vs));
{
    
    struct node *head = nodes_filter(stack->head, p);
    
    stack->head = head;
    
    
    
}

void nodes_dispose(struct node *n)

//@ requires nodes(n, ?vs);
//@ ensures true;
{
    
    if (n != 0)
    {
        nodes_dispose(n->next);
        free(n);
    }
}

void stack_dispose(struct stack *stack)

//@ requires stack(stack, ?vs);
//@ ensures true;
{
    
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