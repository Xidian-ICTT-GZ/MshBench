#include "stdlib.h"

/*@ predicate stack(struct stack *s; struct node *head) = s->head |-> head; @*/
/*@ predicate nodes(struct node *n) =
    n == 0 ?
        true
    :
        n->next |-> ?next &*& n->value |-> ?value &*& nodes(next);
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
//@ requires stack(stack, ?old_head) &*& nodes(old_head);
//@ ensures stack(stack, ?new_head) &*& nodes(new_head);
{
    
    struct node *n = malloc(sizeof(struct node));
    if (n == 0)
    {
        abort();
    }
    //@ open stack(stack, old_head);
    n->next = stack->head;
    n->value = value;
    stack->head = n;
    //@ close nodes(n);
    //@ close stack(stack, n);
    
    
}

void stack_dispose(struct stack *stack)
//@ requires stack(stack, ?head) &*& nodes(head);
//@ ensures true;
{
    //@ open stack(stack, head);
    //@ open nodes(head);
    free(stack);
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}