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

predicate nodes_sum_pred(*mut Node nodes, i32 sum) =
    nodes == null ?
        true
    :
        exists(?value, ?next, ?rest_sum,
            node_pred(nodes, value, next) &*&
            nodes_sum_pred(next, rest_sum) &*&
            sum == value + rest_sum
        );

predicate stack_pred(*mut Stack s, *mut Node head) =
    s->head |-> head;

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32 {
    requires(nodes_sum_pred(nodes, ?sum));
    ensures(nodes_sum_pred(nodes, sum) &*& result == sum);
    let mut result = 0;

    if !nodes.is_null() {
        open nodes_sum_pred(nodes, _);
        assert node_pred(nodes, ?value, ?next);
        assert nodes_sum_pred(next, ?rest_sum);
        close node_pred(nodes, value, next);
        result = get_nodes_sum(next);
        result += value;
        close nodes_sum_pred(nodes, value + rest_sum);
    } else {
        close nodes_sum_pred(nodes, 0);
    }

    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        requires(exists(?head, ?sum,
            stack_pred(stack, head) &*&
            nodes_sum_pred(head, sum)
        ));
        ensures(exists(?head, ?sum,
            stack_pred(stack, head) &*&
            nodes_sum_pred(head, sum) &*&
            result == sum
        ));
        open exists(?head, ?sum, _);
        assert stack_pred(stack, head);
        assert nodes_sum_pred(head, sum);
        close stack_pred(stack, head);
        close nodes_sum_pred(head, sum);
        let result = get_nodes_sum(head);
        result
    }
}