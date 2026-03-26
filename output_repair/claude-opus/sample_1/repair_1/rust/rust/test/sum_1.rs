struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn node_owned(n: *mut Node) -> bool {
    n != std::ptr::null_mut() ==> 
    (exists v: i32, nxt: *mut Node :: 
     points_to(n, Node { value: v, next: nxt }) * node_owned(nxt))
}

#[predicate]
fn node_owned_null(n: *mut Node) -> bool {
    n == std::ptr::null_mut() || node_owned(n)
}

#[predicate]
fn stack_owned(s: *mut Stack) -> bool {
    exists h: *mut Node :: 
    points_to(s, Stack { head: h }) * node_owned_null(h)
}

#[requires(node_owned_null(nodes))]
#[ensures(node_owned_null(nodes))]
unsafe fn get_nodes_sum(nodes: *mut Node) -> i32 {
    let mut result = 0;

    if !nodes.is_null() {
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }

    result
}

impl Stack {
    #[requires(stack_owned(stack))]
    #[ensures(stack_owned(stack))]
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        let result = get_nodes_sum((*stack).head);

        result
    }
}