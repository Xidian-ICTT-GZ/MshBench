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


use std::ptr;

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate node_pred(*mut Node n, i32 value, *mut Node next) =
    n->value |-> value &*& n->next |-> next;

predicate nodes_list(*mut Node nodes) =
    nodes == null ?
        true
    :
        exists(?value, ?next) &*&
        node_pred(nodes, value, next) &*&
        nodes_list(next);

predicate stack_pred(*mut Stack stack, *mut Node head) =
    stack->head |-> head &*& nodes_list(head);

fixpoint i32 sum_nodes(*mut Node nodes) {
    match nodes {
        null => 0,
        _ => {
            let value = nodes->value;
            let next = nodes->next;
            value + sum_nodes(next)
        }
    }
}

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
    requires nodes_list(nodes),
    ensures nodes_list(nodes) &*& result == sum_nodes(nodes)
{
    let mut result = 0;

    if !nodes.is_null() {
        let value = (*nodes).value;
        let next = (*nodes).next;
        close node_pred(nodes, value, next);
        close nodes_list(nodes);
        result = get_nodes_sum(next);
        open nodes_list(nodes);
        open node_pred(nodes, value, next);
        result += value;
    }

    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
        requires stack_pred(stack, ?head),
        ensures stack_pred(stack, head) &*& result == sum_nodes(head)
    {
        let head = (*stack).head;
        close nodes_list(head);
        let result = get_nodes_sum(head);
        open nodes_list(head);
        result
    }
}