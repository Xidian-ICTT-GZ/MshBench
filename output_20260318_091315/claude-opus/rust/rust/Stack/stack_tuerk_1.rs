predicate node(struct Node *n; ) =
    n->next |-> ?next;

predicate stack(struct Stack *stack, int count) =
    count == 0 ?
        stack->head |-> null
    :
        stack->head |-> ?h &*& nodes_list(h, count);

predicate nodes_list(struct Node *node, int count) =
    count > 0 &*& node != null &*& node->next |-> ?next &*&
    nodes_list(next, count - 1);

#[requires(stack(stk, ?c))]
#[ensures(stack(stk, c) &*& result == c)]
unsafe fn stack_get_count(stack: *mut Stack) -> i32
{
    let mut n = (*stack).head;
    let mut i = 0;
    #[invariant(stack(stk, c) &*& nodes_list_prefix(n, i, c))]
    loop {
        if n.is_null() {
            break;
        }
        n = (*n).next;
        i += 1;
    }
    i
}

predicate nodes_list_prefix(struct Node *node, int prefix_len, int total_len) =
    prefix_len == 0 ?
        true
    :
        node != null &*& node->next |-> ?next &*&
        nodes_list_prefix(next, prefix_len - 1, total_len - 1);