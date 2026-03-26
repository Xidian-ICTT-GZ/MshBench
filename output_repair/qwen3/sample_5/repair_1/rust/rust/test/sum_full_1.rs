use std::ptr;

predicate NodePtr(node: *mut Node, tail_pred: pred) =
    node != null() && (*node).next == tail_pred;

predicate StackPtr(stack: *mut Stack, head_pred: pred) =
    stack != null() && (*stack).head == head_pred;

lemma fn get_nodes_sum_spec(node: *mut Node) -> i32
    requires node != null() ==> NodePtr(node, true)
    ensures result == 0 || (node != null() && result == (*node).value + get_nodes_sum((*node).next))
{
    if node.is_null() {
        return 0;
    }
    let tail_sum = get_nodes_sum((*node).next);
    let res = (*node).value + tail_sum;
    return res;
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
        requires StackPtr(stack, true)
        ensures result == 0 || (stack != null() && result == get_nodes_sum((*stack).head))
    {
        let result = get_nodes_sum((*stack).head);
        result
    }
}