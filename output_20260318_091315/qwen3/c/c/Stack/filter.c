/*@ predicate node(struct node *n; int v, struct node *next) =
    n != 0 &*&
    malloc_block_node(n) &*&
    n->value |-> v &*&
    n->next |-> next;
@*/

/*@ predicate stack(struct stack *s; list<int> vs) =
    s != 0 &*&
    malloc_block_stack(s) &*&
    s->head |-> ?head &*&
    nodes(head, vs);
@*/

/*@ predicate nodes(struct node *n; list<int> vs) =
    n == 0 ?
        vs == nil
    :
        vs == cons(?v, ?vs0) &*&
        node(n, v, ?next) &*&
        nodes(next, vs0);
@*/

/*@ lemma void nodes_nil()
    requires nodes(0, ?vs);
    ensures vs == nil;
{
}
@*/

/*@ lemma void nodes_cons()
    requires nodes(?n, ?vs) &*& n != 0;
    ensures vs == cons(?v, ?vs0) &*& node(n, v, ?next) &*& nodes(next, vs0);
{
}
@*/

/*@ lemma void nodes_split(list<int> vs)
    requires nodes(?n, vs);
    ensures
        n == 0 ?
            vs == nil
        :
            vs == cons(?v, ?vs0) &*& node(n, v, ?next) &*& nodes(next, vs0);
{
}
@*/

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

/*@ predicate int_predicate(int_predicate *p;) = true; @*/

struct node *nodes_filter(struct node *n, int_predicate *p)
//@ requires nodes(n, ?vs) &*& int_predicate(p);
//@ ensures nodes(result, ?vs_filtered) &*& filter(p, vs, vs_filtered);
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

/*@ predicate filter(int_predicate *p, list<int> vs, list<int> ws) =
    vs == nil ?
        ws == nil
    :
        vs == cons(?v, ?vs0) &*&
        (p(v) ?
            ws == cons(v, ?ws0) &*& filter(p, vs0, ws0)
        :
            filter(p, vs0, ws));
@*/

void stack_filter(struct stack *stack, int_predicate *p)
//@ requires stack(stack, ?vs) &*& int_predicate(p);
//@ ensures stack(stack, ?ws) &*& filter(p, vs, ws);
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