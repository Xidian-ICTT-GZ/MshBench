#include "stdlib.h"

struct node
{
    struct node *next;
    int value;
};

/*@ predicate nodes(struct node *n; list<int> vs) =
      n == 0 ?
        vs == nil
      :
        n->value |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*&
        nodes(next, ?rest) &*& vs == cons(v, rest);
@*/

struct stack
{
    struct node *head;
};

/*@ predicate stack(struct stack *stack; list<int> contents) =
      stack->head |-> ?head &*& malloc_block_stack(stack) &*& nodes(head, contents);
@*/

struct stack *create_stack()
/*@ requires true; @*/
/*@ ensures stack(result, nil); @*/
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
/*@ requires stack(stack, ?contents); @*/
/*@ ensures stack(stack, cons(value, contents)); @*/
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
/*@ requires stack(stack, ?contents) &*& contents != nil; @*/
/*@ ensures stack(stack, tail(contents)) &*& result == head(contents); @*/
{
    struct node *head = stack->head;
    
    int result = head->value;
    stack->head = head->next;
    free(head);
    
    return result;
}

typedef bool int_predicate(int x);

/*@ 
fixpoint bool pred_applies(int_predicate *p, int x);

fixpoint list<int> filter_list(int_predicate *p, list<int> xs) {
  switch(xs) {
    case nil: return nil;
    case cons(x, xs0): return pred_applies(p, x) ? cons(x, filter_list(p, xs0)) : filter_list(p, xs0);
  }
} 
@*/

/*@ 
predicate nodes_filter_pred(struct node *n; list<int> vs, int_predicate *p) =
    n == 0 ? vs == nil
    : exists<int> v, struct node *next;
      n->value |-> v &*& n->next |-> next &*& malloc_block_node(n) &*&
      nodes_filter_pred(next, ?rest, p) &*&
      vs == (pred_applies(p, v) ? cons(v, rest) : rest);
@*/

/*@ 
lemma void nodes_filter_relate(struct node *n, list<int> vs, int_predicate *p)
  requires nodes(n, vs);
  ensures nodes_filter_pred(n, filter_list(p, vs), p);
{
  switch(n) {
    case 0:
    case null: return;
    default:
      open nodes(n, vs);
      open nodes(n->next, ?rest);
      nodes_filter_relate(n->next, rest, p);
      close nodes_filter_pred(n, filter_list(p, vs), p);
      close nodes(n, vs);
  }
}
@*/

struct node *nodes_filter(struct node *n, int_predicate *p)
/*@ requires nodes(n, ?vs) &*& int_predicate(p); @*/
/*@ ensures nodes_filter_pred(result, filter_list(p, vs), p); @*/
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
/*@ requires stack(stack, ?contents) &*& int_predicate(p); @*/
/*@ ensures stack(stack, filter_list(p, contents)); @*/
{
    struct node *head = nodes_filter(stack->head, p);
    stack->head = head;
}

void nodes_dispose(struct node *n)
/*@ requires nodes(n, ?vs); @*/
/*@ ensures true; @*/
{
    if (n != 0)
    {
        nodes_dispose(n->next);
        free(n);
    }
}

void stack_dispose(struct stack *stack)
/*@ requires stack(stack, ?contents); @*/
/*@ ensures true; @*/
{
    nodes_dispose(stack->head);
    free(stack);
}

bool neq_20(int x)
/*@ requires true; @*/
/*@ ensures true; @*/
{
    return x != 20;
}

int main()
/*@ requires true; @*/
/*@ ensures true; @*/
{
    struct stack *s = create_stack();
    stack_push(s, 10);
    stack_push(s, 20);
    stack_push(s, 30);
    stack_filter(s, neq_20);
    stack_dispose(s);
    return 0;
}