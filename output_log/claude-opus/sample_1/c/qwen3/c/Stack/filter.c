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

/*@ predicate stack(struct stack *s; struct node *head) =
    s != 0 &*& valid(s) &*& s->head |-> head &*&
    node_list(head, ?nodes) @*/

/*@ predicate node_list(struct node *n; list<int> values) =
    n == 0 ? values == nil :
    n != 0 &*&
    n->next |-> ?next &*&
    n->value |-> ?v &*&
    node_list(next, ?tail) &*&
    values == cons(v, tail) @*/

/*@ predicate node(struct node *n; int value, struct node *next) =
    n != 0 &*&
    n->value |-> value &*&
    n->next |-> next @*/

/*@ lemma void node_list_append(struct node *n, list<int> l1, list<int> l2)
    requires node_list(n, append(l1, l2));
    ensures node_list(n, l1) &*& node_list(?m, l2) &*& (l1 == nil ==> m == n) &*& (l1 != nil ==> n != 0 &*& n->next |-> m);
{
    if (l1 == nil) {
        // n must be the start of l2
    } else {
        open node_list(n, append(l1, l2));
        assert n != 0;
        struct node *next;
        int v;
        leak n->next |-> next;
        leak n->value |-> v;
        close node(n, v, next);
        node_list_append(next, tail(l1), l2);
        close node_list(n, l1);
    }
} @*/

struct stack *create_stack()

{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0)
    {
        abort();
    }
    //@ assume stack != 0;
    //@ alloc_heap(stack, sizeof(struct stack));
    //@ assume stack->head |-> ?h;
    stack->head = 0;

    //@ close node_list(0, nil);
    //@ close stack(stack, 0);
    return stack;
}

void stack_push(struct stack *stack, int value)

{
    //@ open stack(stack, ?head);
    struct node *n = malloc(sizeof(struct node));
    if (n == 0)
    {
        abort();
    }
    //@ assume n != 0;
    //@ alloc_heap(n, sizeof(struct node));
    //@ assume n->next |-> ?next;
    //@ assume n->value |-> ?val;
    n->next = stack->head;
    n->value = value;
    stack->head = n;

    //@ close node(n, value, head);
    //@ close node_list(n, cons(value, ?tail));
    //@ close stack(stack, n);
}

int stack_pop(struct stack *stack)

{
    //@ open stack(stack, ?head);
    struct node *head = stack->head;

    //@ assume head != 0;
    //@ open node_list(head, cons(?v, ?tail));
    //@ open node(head, v, ?next);
    int result = head->value;
    stack->head = head->next;
    free(head);

    //@ close node_list(next, tail);
    //@ close stack(stack, next);
    return result;
}

typedef bool int_predicate(int x);

/*@ 
  predicate nodes_filter_pred(struct node *n; list<int> vals, int_predicate *p) =
    n == 0 ? vals == nil :
    n != 0 &*&
    n->value |-> ?v &*&
    n->next |-> ?next &*&
    p(v) == true ? nodes_filter_pred(next, ?filtered_tail, p) &*& vals == cons(v, filtered_tail)
               : nodes_filter_pred(next, vals, p);
@*/

struct node *nodes_filter(struct node *n, int_predicate *p)

{
    if (n == 0)
    {
        //@ close node_list(0, nil);
        return 0;
    }
    else
    {
        //@ open node_list(n, cons(?v, ?tail));
        //@ open node(n, v, ?next);
        bool keep = p(n->value);
        if (keep)
        {
            struct node *next_filtered = nodes_filter(n->next, p);
            //@ open node_list(next, ?next_vals);
            //@ close node(n, v, next_filtered);
            n->next = next_filtered;
            //@ close node_list(n, cons(v, ?filtered_tail));
            return n;
        }
        else
        {
            struct node *next = n->next;
            free(n);
            struct node *result = nodes_filter(next, p);
            //@ close node_list(result, ?filtered_tail);
            return result;
        }
    }
}

void stack_filter(struct stack *stack, int_predicate *p)

{
    //@ open stack(stack, ?head);
    struct node *head = nodes_filter(stack->head, p);
    stack->head = head;
    //@ close stack(stack, head);
}

void nodes_dispose(struct node *n)

{
    if (n != 0)
    {
        //@ open node_list(n, cons(?v, ?tail));
        //@ open node(n, v, ?next);
        nodes_dispose(n->next);
        free(n);
    }
}

void stack_dispose(struct stack *stack)

{
    //@ open stack(stack, ?head);
    nodes_dispose(stack->head);
    free(stack);
}

bool neq_20(int x)

{
    return x != 20;
}

int main()

{
    struct stack *s = create_stack();
    stack_push(s, 10);
    stack_push(s, 20);
    stack_push(s, 30);
    stack_filter(s, neq_20);
    stack_dispose(s);
    return 0;
}