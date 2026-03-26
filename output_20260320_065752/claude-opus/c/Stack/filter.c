#include "stdlib.h"

struct node
{
    struct node *next;
    int value;
};

/*@ predicate nodes(struct node *n;) =
      n == 0 ? true : malloc_block_node(n) &*&
        nodes(n->next) &*& n->value |-> _ &*& n->next |-> _;
@*/

struct stack
{
    struct node *head;
};

/*@ predicate malloc_block_node(struct node *p;) = malloc_block(p, sizeof(struct node)); @*/
/*@ predicate malloc_block_stack(struct stack *p;) = malloc_block(p, sizeof(struct stack)); @*/

/*@ predicate stack(struct stack *stack;) = 
      stack != 0 &*& 
      malloc_block_stack(stack) &*& 
      nodes(stack->head) &*& stack->head |-> _; 
@*/

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
    struct node *n = malloc(sizeof(struct node));
    if (n == 0)
    {
        abort();
    }
    n->next = stack->head;
    n->value = value;
    stack->head = n;
    //@ open stack(stack);
    //@ close nodes(n);
    //@ close stack(stack);
}

int stack_pop(struct stack *stack)
    //@ requires stack(stack) &*& stack->head != 0;
    //@ ensures stack(stack);
{
    //@ open stack(stack);
    struct node *head = stack->head;
    
    int result = head->value;
    stack->head = head->next;
    //@ open nodes(head);
    free(head);
    //@ close stack(stack);
    return result;
}

typedef bool int_predicate(int x);
/*@

predicate_family nodes_predicates(int_predicate *p)(struct node *n) =
    n == 0 ? true : malloc_block_node(n) &*&
    nodes_predicates(p)(n->next) &*& n->value |-> ?v &*& n->next |-> _;

@*/

struct node *nodes_filter(struct node *n, int_predicate *p)
    //@ requires nodes_predicates(p)(n) &*& p(|_)->requires(true); 
    //@ ensures nodes_predicates(p)(result);
{
    if (n == 0)
    {
        return 0;
    }
    else
    {
        //@ open nodes_predicates(p)(n);
        bool keep = p(n->value);
        if (keep)
        {
            struct node *next = nodes_filter(n->next, p);
            n->next = next;
            //@ close nodes_predicates(p)(n);
            return n;
        }
        else
        {
            struct node *next = n->next;
            free(n);
            struct node *result = nodes_filter(next, p);
            //@ close nodes_predicates(p)(result);
            return result;
        }
    }
}

void stack_filter(struct stack *stack, int_predicate *p)
    //@ requires stack(stack) &*& p(|_)->requires(true);
    //@ ensures stack(stack);
{
    //@ open stack(stack);
    //@ open nodes(stack->head);
    //@ close nodes_predicates(p)(stack->head);
    struct node *head = nodes_filter(stack->head, p);
    stack->head = head;
    //@ close stack(stack);
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
    //@ requires stack(stack);
    //@ ensures true;
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