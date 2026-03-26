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


#[predicate]
pred node(node: *mut Node, value: i32, next: *mut Node) = (*node).value |-> value &*& (*node).next |-> next;

#[predicate]
pred stack(stack: *mut Stack, head: *mut Node) = (*stack).head |-> head;

unsafe fn get_nodes_sum(node: *mut Node) -> i32
    requires node == std::ptr::null_mut::<Node>() ? emp : exists(?v, ?n) &*& node(node, v, n);
    ensures node == std::ptr::null_mut::<Node>() ? result == 0 : exists(?v, ?n) &*& node(node, v, n) &*& result == v + get_nodes_sum(n);
{
    let mut result = 0;
    if !node.is_null() {
        open node(node, _, _);
        let tail_sum = get_nodes_sum((*node).next);
        close node(node, (*node).value, (*node).next);
        result = (*node).value + tail_sum;
    }

    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
        requires stack(stack, ?head) &*& head == std::ptr::null_mut::<Node>() ? emp : exists(?v, ?n) &*& node(head, v, n);
        ensures stack(stack, head) &*& head == std::ptr::null_mut::<Node>() ? result == 0 : exists(?v, ?n) &*& node(head, v, n) &*& result == v + get_nodes_sum(n);
    {
        open stack(stack, _);
        let result = get_nodes_sum((*stack).head);
        close stack(stack, (*stack).head);

        result
    }
}