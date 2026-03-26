unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
{
    #[requires(nodes == std::ptr::null_mut() || nodes |-> Node { next: ?next, value: ?val } * node_list(?next))]
    #[ensures(nodes == std::ptr:: null_mut() ==> result == 0)]
    #[ensures(nodes != std::ptr::null_mut() ==> result == ?val + ?sum_next && node_list(nodes))]
    let mut result = 0;

    if !nodes.is_null() {
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }

    result
}

predicate node_list(*mut Node nodes;) =
    match nodes {
        std::ptr::null_mut() => emp,
        _ => nodes |-> Node { next: ?next, value: _ } * node_list(next)
    };

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
    {
        #[requires(stack |-> Stack { head: ?head } * node_list(?head))]
        #[ensures(stack |-> Stack { head: ?head } * node_list(?head) && result == ?sum && sum_node_list(?head, ?sum))]
        let result = get_nodes_sum((*stack).head);

        result
    }
}

predicate sum_node_list(*mut Node nodes, i32 sum;) =
    match nodes {
        std::ptr::null_mut() => sum == 0,
        _ => nodes |-> Node { next: ?next, value: ?val } * sum_node_list(next, ?sum_rest) && sum == val + sum_rest
    };