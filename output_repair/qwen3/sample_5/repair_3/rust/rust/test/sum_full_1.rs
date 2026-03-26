unsafe fn get_nodes_sum(node: *mut Node) -> i32 {
    let mut result = 0;
    if !node.is_null() {
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
    }

    result
}
impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        let result = get_nodes_sum((*stack).head);

        result
    }
}


unsafe fn get_nodes_sum(node: *mut Node) -> i32 {
    let mut result = 0;
    if !node.is_null() {
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
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

predicate node_pred(node: *mut Node; next: *mut Node, value: i32) =
    node != null() && (*node).next |-> next &*& (*node).value |-> value;

predicate nodes_pred(node: *mut Node) =
    node == null()
    || exists(next: *mut Node, value: i32).
       node_pred(node, next, value) * nodes_pred(next);

predicate stack_pred(stack: *mut Stack; head: *mut Node) =
    stack != null() && (*stack).head |-> head;

predicate stack_full(stack: *mut Stack) =
    exists(head: *mut Node).
    stack_pred(stack, head) * nodes_pred(head);

lemma fn nodes_sum_lemma(node: *mut Node) -> i32
    requires nodes_pred(node)
    ensures nodes_pred(node) &*& result == sum_nodes(node)
{
    if node == null() {
        return 0;
    } else {
        open nodes_pred(node);
        let next = (*node).next;
        let value = (*node).value;
        let tail_sum = nodes_sum_lemma(next);
        close nodes_pred(node);
        return value + tail_sum;
    }
}

pure fn sum_nodes(node: *mut Node) -> i32 {
    if node == null() {
        0
    } else {
        (*node).value + sum_nodes((*node).next)
    }
}

unsafe fn get_nodes_sum(node: *mut Node) -> i32
    requires nodes_pred(node)
    ensures nodes_pred(node) &*& result == sum_nodes(node)
{
    let mut result = 0;
    if node != null() {
        open nodes_pred(node);
        let next = (*node).next;
        let value = (*node).value;
        let tail_sum = get_nodes_sum(next);
        result = value + tail_sum;
        close nodes_pred(node);
    }
    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
        requires stack_full(stack)
        ensures stack_full(stack) &*& result == sum_nodes((*stack).head)
    {
        open stack_full(stack);
        open stack_pred(stack, _);
        let head = (*stack).head;
        let s = get_nodes_sum(head);
        close stack_pred(stack, head);
        close stack_full(stack);
        s
    }
}