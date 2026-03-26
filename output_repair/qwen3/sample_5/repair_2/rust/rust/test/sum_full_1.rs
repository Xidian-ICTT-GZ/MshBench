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

predicate Node(node: *mut Node; next: *mut Node, value: i32) =
    node != null() && (*node).next |-> next &*& (*node).value |-> value;

predicate Nodes(node: *mut Node) =
    node == null()
    || exists(next: *mut Node, value: i32).
       Node(node, next, value) * Nodes(next);

predicate Stack(stack: *mut Stack; head: *mut Node) =
    stack != null() && (*stack).head |-> head;

predicate Stack_full(stack: *mut Stack) =
    exists(head: *mut Node).
    Stack(stack, head) * Nodes(head);

lemma fn nodes_sum_lemma(node: *mut Node) -> i32
    requires Nodes(node)
    ensures Nodes(node) &*& result == sum_nodes(node)
{
    if node == null() {
        return 0;
    } else {
        open Nodes(node);
        let next = (*node).next;
        let value = (*node).value;
        let tail_sum = nodes_sum_lemma(next);
        close Nodes(node);
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
    requires Nodes(node)
    ensures Nodes(node) &*& result == sum_nodes(node)
{
    let mut result = 0;
    if node != null() {
        open Nodes(node);
        let next = (*node).next;
        let value = (*node).value;
        let tail_sum = get_nodes_sum(next);
        result = value + tail_sum;
        close Nodes(node);
    }
    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
        requires Stack_full(stack)
        ensures Stack_full(stack) &*& result == sum_nodes((*stack).head)
    {
        open Stack_full(stack);
        open Stack(stack, _);
        let head = (*stack).head;
        let s = get_nodes_sum(head);
        close Stack(stack, head);
        close Stack_full(stack);
        s
    }
}