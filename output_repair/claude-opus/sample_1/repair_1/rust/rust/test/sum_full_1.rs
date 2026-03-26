struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate node_list(node: *mut Node, sum: i32) =
    node.is_null() ? sum == 0 : 
    exists<tail_sum: i32> (
        (*node).value + tail_sum == sum &&
        node_list((*node).next, tail_sum)
    );

#[requires(node_list(node, _))]
#[ensures(node_list(node, result))]
unsafe fn get_nodes_sum(node: *mut Node) -> i32 {
    let mut result = 0;
    if !node.is_null() {
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
    }
    result
}

impl Stack {
    #[requires(exists<sum: i32> node_list((*stack).head, sum))]
    #[ensures(exists<sum: i32> node_list((*stack).head, sum) && result == sum)]
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        let result = get_nodes_sum((*stack).head);
        result
    }
}