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
pred node_pred(node: *mut Node, value: i32, next: *mut Node) = (*node).value |-> value &*& (*node).next |-> next;

#[predicate]
pred stack_pred(stack: *mut Stack, head: *mut Node) = (*stack).head |-> head;

unsafe fn get_nodes_sum(node: *mut Node) -> i32
    requires node == std::ptr::null_mut::<Node>() ? emp : exists(?v) &*& exists(?n) &*& node_pred(node, v, n);
    ensures node == std::ptr::null_mut::<Node>() ? emp : exists(?v) &*& exists(?n) &*& node_pred(node, v, n) &*& result == if node == std::ptr::null_mut::<Node>() { 0 } else { v + get_nodes_sum(n) };
{
    let mut result = 0;
    if !node.is_null() {
        open node_pred(node, _, _);
        let tail_sum = get_nodes_sum((*node).next);
        close node_pred(node, (*node).value, (*node).next);
        result = (*node).value + tail_sum;
    }

    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
        requires exists(?h) &*& stack_pred(stack, h);
        ensures exists(?h) &*& stack_pred(stack, h) &*& result == if h == std::ptr::null_mut::<Node>() { 0 } else { get_nodes_sum(h) };
    {
        open stack_pred(stack, _);
        let result = get_nodes_sum((*stack).head);
        close stack_pred(stack, (*stack).head);
        result
    }
}