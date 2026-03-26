/*@ predicate stack(struct stack *s; struct node *h) = s->head |-> h; @*/

/*@ predicate nodes(struct node *n; list<int> vs) =
    n == 0 ?
        vs == nil
    :
        n->next |-> ?next &*& n->value |-> ?v &*& malloc_block_node(n) &*& nodes(next, ?vs0) &*& vs == cons(v, vs0);
@*/

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
    return stack;
}

void stack_push(struct stack *stack, int value)
//@ requires stack(stack, ?old_head) &*& malloc_block_stack(stack);
//@ ensures stack(stack, ?new_head) &*& malloc_block_stack(stack) &*& nodes(new_head, cons(value, ?vs)) &*& nodes(old_head, vs);
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
//@ requires stack(stack, ?h) &*& malloc_block_stack(stack);
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