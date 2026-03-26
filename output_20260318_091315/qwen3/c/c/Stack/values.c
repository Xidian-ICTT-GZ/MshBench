/*@ predicate stack(struct stack *s; list<int> values) =
    s->head |-> ?head &*& 
    (head == 0 ? 
        values == nil 
    : 
        node(head, values)
    );
@*/

/*@ predicate node(struct node *n; list<int> values) =
    n->next |-> ?next &*& n->value |-> ?v &*&
    (next == 0 ? 
        values == cons(v, nil)
    :
        node(next, ?tail) &*& values == cons(v, tail)
    );
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

void stack_dispose(struct stack *stack)
//@ requires stack(stack, _);
//@ ensures true;
{
    free(stack);
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}