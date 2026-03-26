#[predicate]
pub pred Node(node: *mut Node, value: i32, next: *mut Node) = (*node).value |-> value &*& (*node).next |-> next;

#[predicate]
pub pred Stack(stack: *mut Stack, head: *mut Node) = (*stack).head |-> head;

unsafe fn get_nodes_sum(node: *mut Node) -> i32
    requires node == null::<Node>() ? emp : exists(?v) &*& exists(?n) &*& Node(node, v, n);
    ensures node == null::<Node>() ? emp : exists(?v) &*& exists(?n) &*& Node(node, v, n) &*& result == if node == null::<Node>() { 0 } else { v + get_nodes_sum(n) };
{
    let mut result = 0;
    if !node.is_null() {
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
    }

    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
        requires exists(?h) &*& Stack(stack, h);
        ensures exists(?h) &*& Stack(stack, h) &*& result == if h == null::<Node>() { 0 } else { get_nodes_sum(h) };
    {
        let result = get_nodes_sum((*stack).head);

        result
    }
}