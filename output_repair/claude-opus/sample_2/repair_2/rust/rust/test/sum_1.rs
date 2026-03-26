struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn node_list(ptr: *mut Node, sum: i32) -> bool {
    if ptr.is_null() {
        sum == 0
    } else {
        exists(|n: Node, rest_sum: i32| {
            points_to(ptr, n) && node_list(n.next, rest_sum) && sum == n.value + rest_sum
        })
    }
}

#[requires(node_list(nodes, _))]
#[ensures(node_list(nodes, _))]
unsafe fn get_nodes_sum(nodes: *mut Node) -> i32 {
    let mut result = 0;

    if !nodes.is_null() {
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }

    result
}

impl Stack {
    #[requires(points_to(stack, Stack { head: ?h }) && node_list(h, _))]
    #[ensures(points_to(stack, Stack { head: ?h }) && node_list(h, _))]
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        let result = get_nodes_sum((*stack).head);
        result
    }
}