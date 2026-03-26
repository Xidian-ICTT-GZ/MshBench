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

/*@
predicate nodes(struct node *n;) =
    n == 0 ? emp : n->next |-> ?next &*& n->value |-> _ &*& malloc_block_node(n) &*& nodes(next);

predicate stack(struct stack *s;) =
    s->head |-> ?head &*& malloc_block_stack(s) &*& nodes(head);

predicate_family_instance int_predicate_pre(int_predicate *p)(int x);
predicate_family_instance int_predicate_post(int_predicate *p)(int x, bool result);
@*/

/*@
predicate_family int_predicate_pre(void *p)(int x);
predicate_family int_predicate_post(void *p)(int x, bool result);
@*/

/*@
typedef bool int_predicate(int x);
    requires int_predicate_pre(this)(x);
    ensures int_predicate_post(this)(x, result);
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
//@ requires stack(stack) &*& stack->head |-> ?head &*& head != 0;
//@ ensures stack(stack);
{
    //@ open stack(stack);
    //@ open nodes(stack->head);
    struct node *head = stack->head;

    int result = head->value;
    stack->head = head->next;
    free(head);
    //@ close stack(stack);
    return result;
}

/*@
predicate_family_instance int_predicate_pre(neq_20)(int x) = true;
predicate_family_instance int_predicate_post(neq_20)(int x, bool result) = result == (x != 20);
@*/

struct node *nodes_filter(struct node *n, int_predicate *p)
//@ requires nodes(n) &*& is_int_predicate(p) == true;
//@ ensures nodes(result) &*& is_int_predicate(p) == true;
{
    //@ open nodes(n);
    if (n == 0)
    {
        //@ close nodes(0);
        return 0;
    }
    else
    {
        //@ close int_predicate_pre(p)(n->value);
        bool keep = p(n->value);
        //@ open int_predicate_post(p)(n->value, keep);
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
//@ requires stack(stack) &*& is_int_predicate(p) == true;
//@ ensures stack(stack) &*& is_int_predicate(p) == true;
{
    //@ open stack(stack);
    struct node *head = nodes_filter(stack->head, p);

    stack->head = head;
    //@ close stack(stack);
}

void nodes_dispose(struct node *n)
//@ requires nodes(n);
//@ ensures true;
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
//@ ensures true;
{
    //@ open stack(stack);
    nodes_dispose(stack->head);
    free(stack);
}

bool neq_20(int x) //@ : int_predicate
//@ requires int_predicate_pre(neq_20)(x);
//@ ensures int_predicate_post(neq_20)(x, result);
{
    //@ open int_predicate_pre(neq_20)(x);
    //@ close int_predicate_post(neq_20)(x, x != 20);
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