#[predicate]
pub pred Node(node: *mut Node, value: i32, next: *mut Node) = (*node).value |-> value &*& (*node).next |-> next;

#[predicate]
pub pred Stack(stack: *mut Stack, head: *mut Node) = (*stack).head |-> head;

unsafe fn get_nodes_sum(node: *mut Node) -> i32
    requires node == null::<Node>() ? emp : exists(?v, ?n) &*& Node(node, v, n);
    ensures node == null::<Node>() ? result == 0 : exists(?v, ?n) &*& Node(node, v, n) &*& result == v + get_nodes_sum(n);
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
        requires Stack(stack, ?head) &*& head == null::<Node>() ? emp : exists(?v, ?n) &*& Node(head, v, n);
        ensures Stack(stack, head) &*& head == null::<Node>() ? result == 0 : exists(?v, ?n) &*& Node(head, v, n) &*& result == v + get_nodes_sum(n);
    {
        let result = get_nodes_sum((*stack).head);

        result
    }
}