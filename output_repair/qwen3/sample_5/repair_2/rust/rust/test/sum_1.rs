unsafe fn get_nodes_sum(nodes: *mut Node) -> i32 {
    let mut result = 0;

    if !nodes.is_null() {
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }

    result
}
impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        let result = get_nodes_sum((*stack).head);

        result
    }
}


predicate node_pred(*mut Node n, i32 value, *mut Node next) =
    n->value |-> value &*& n->next |-> next;

predicate stack_pred(*mut Stack s, *mut Node head) =
    s->head |-> head;

predicate nodes_sum(*mut Node nodes, i32 sum) =
    nodes == null ?
        sum == 0
    :
        exists(i32 v, *mut Node next,
            node_pred(nodes, v, next) &*& nodes_sum(next, sum - v)
        );

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
    requires nodes_sum(nodes, ?sum);
    ensures nodes_sum(nodes, sum) &*& result == sum;
{
    let mut result = 0;

    if !nodes.is_null() {
        let v = (*nodes).value;
        let next = (*nodes).next;
        close node_pred(nodes, v, next)();
        assert nodes_sum(nodes, ?s);
        open nodes_sum(nodes, s)();
        result = get_nodes_sum(next);
        result += v;
        close nodes_sum(nodes, result)();
    }

    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
        requires stack_pred(stack, ?head) &*& nodes_sum(head, ?sum);
        ensures stack_pred(stack, head) &*& nodes_sum(head, sum) &*& result == sum;
    {
        let result = get_nodes_sum((*stack).head);

        result
    }
}