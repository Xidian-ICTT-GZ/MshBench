pred nodes(node: *mut Node; sum: i32) =
    node == std::ptr::null_mut() ?
        sum == 0
    :
        (*node).value |-> ?v &*& (*node).next |-> ?next &*& nodes(next, ?tail_sum) &*& sum == v + tail_sum;

pred stack(stack: *mut Stack; sum: i32) =
    (*stack).head |-> ?head &*& nodes(head, sum);

#[requires(nodes(node, ?sum))]
#[ensures(nodes(node, sum) &*& result == sum)]
unsafe fn get_nodes_sum(node: *mut Node) -> i32 {
    let mut result = 0;
    if !node.is_null() {
        #[open nodes(node, sum)]
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
        #[close nodes(node, sum)]
    }

    result
}

impl Stack {
    #[requires(stack(stack, ?sum))]
    #[ensures(stack(stack, sum) &*& result == sum)]
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        let result = get_nodes_sum((*stack).head);

        result
    }
}