//@ #include "ghost_sequences.gh"

/*@ 
predicate node(struct node *n; int value, struct node *next) =
    n != 0 &*&
    malloc_block_node(n) &*&
    struct_node_next(n, next) &*&
    struct_node_value(n, value);
@*/

/*@ 
predicate stack(struct stack *s; list<int> values) =
    s != 0 &*&
    malloc_block_stack(s) &*&
    struct_stack_head(s, ?head) &*&
    nodes(head, values);
@*/

/*@ 
predicate nodes(struct node *n; list<int> values) =
    n == 0 ? values == nil : 
    values == cons(?v, ?vs) &*& node(n, v, ?next) &*& nodes(next, vs);
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
//@ requires stack(stack, ?values);
//@ ensures stack(stack, cons(value, values));
{
    //@ open stack(stack, values);
    struct node *n = malloc(sizeof(struct node));
    if (n == 0)
    {
        abort();
    }
    n->next = stack->head;
    n->value = value;
    stack->head = n;
    //@ close node(n, value, stack->head);
    //@ close nodes(n, cons(value, values));
    //@ close stack(stack, cons(value, values));
}

int stack_pop(struct stack *stack)
//@ requires stack(stack, cons(?value, ?values));
//@ ensures stack(stack, values) &*& result == value;
{
    //@ open stack(stack, cons(value, values));
    struct node *head = stack->head;
    //@ open nodes(head, cons(value, values));
    //@ open node(head, value, ?next);
    int result = head->value;
    stack->head = head->next;
    free(head);
    //@ close stack(stack, values);
    return result;
}

typedef bool int_predicate(int x);

struct node *nodes_filter(struct node *n, int_predicate *p)
//@ requires nodes(n, ?values) &*& ints_forall(values, (int)(p));
//@ ensures nodes(result, filter(p, values));
{
    if (n == 0)
    {
        //@ close nodes(0, nil);
        return 0;
    }
    else
    {
        //@ open nodes(n, cons(?v, ?vs));
        //@ open node(n, v, ?next);
        bool keep = p(n->value);
        if (keep)
        {
            struct node *next = nodes_filter(n->next, p);
            //@ assert nodes(next, filter(p, vs));
            n->next = next;
            //@ close node(n, v, next);
            //@ close nodes(n, cons(v, filter(p, vs)));
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
//@ requires stack(stack, ?values) &*& ints_forall(values, (int)(p));
//@ ensures stack(stack, filter(p, values));
{
    //@ open stack(stack, values);
    struct node *head = nodes_filter(stack->head, p);
    stack->head = head;
    //@ close stack(stack, filter(p, values));
}

void nodes_dispose(struct node *n)
//@ requires nodes(n, ?values);
//@ ensures true;
{
    if (n != 0)
    {
        //@ open nodes(n, cons(?v, ?vs));
        //@ open node(n, v, ?next);
        nodes_dispose(n->next);
        free(n);
    }
}

void stack_dispose(struct stack *stack)
//@ requires stack(stack, ?values);
//@ ensures true;
{
    //@ open stack(stack, values);
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