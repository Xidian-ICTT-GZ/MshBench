unsafe fn get_nodes_sum(node: *mut Node) -> i32
{
    #[requires(node == std::ptr::null_mut() || node |-> Node { next: ?next, value: ?value } * get_nodes_sum_nodes(?next))]
    #[ensures(node == std::ptr::null_mut() || node |-> Node { next: ?next, value: ?value } * get_nodes_sum_nodes(?next) && result == ?value + get_nodes_sum_result(?next))]
    let mut result = 0;
    if !node.is_null() {
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
    }

    result
}

predicate get_nodes_sum_nodes(*mut Node node) =
    match node {
        std::ptr::null_mut() => emp,
        _ => node |-> Node { next: ?next, value: _ } * get_nodes_sum_nodes(next)
    };

predicate_family get_nodes_sum_result(*mut Node node; i32 sum) =
    match node {
        std::ptr::null_mut() => sum == 0,
        _ => node |-> Node { next: ?next, value: ?value } * get_nodes_sum_nodes(next) * get_nodes_sum_result(next, ?tail_sum) &*& sum == value + tail_sum
    };

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
    {
        #[requires(stack |-> Stack { head: ?head } * get_nodes_sum_nodes(?head))]
        #[ensures(stack |-> Stack { head: ?head } * get_nodes_sum_nodes(?head) && result == get_nodes_sum_result_value(?head))]
        let result = get_nodes_sum((*stack).head);

        result
    }
}

predicate_family get_nodes_sum_result_value(*mut Node node; i32 sum) =
    match node {
        std::ptr::null_mut() => sum == 0,
        _ => node |-> Node { next: ?next, value: ?value } * get_nodes_sum_nodes(next) * get_nodes_sum_result_value(next, ?tail_sum) &*& sum == value + tail_sum
    };