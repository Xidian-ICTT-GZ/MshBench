struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn node_own(n: *mut Node) -> bool {
    n != std::ptr::null_mut() ==> 
    (exists v: i32, nxt: *mut Node :: 
     points_to(n, Node { value: v, next: nxt }) * node_own(nxt))
}

#[predicate]
fn node_own_null(n: *mut Node) -> bool {
    n == std::ptr::null_mut()
}

#[predicate]
fn stack_own(s: *mut Stack, h: *mut Node) -> bool {
    points_to(s, Stack { head: h }) * node_own(h)
}

#[requires(node_own(nodes))]
#[ensures(node_own(nodes))]
unsafe fn get_nodes_sum(nodes: *mut Node) -> i32 {
    let mut result = 0;

    if !nodes.is_null() {
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }

    result
}

impl Stack {
    #[requires(stack_own(stack, (*stack).head))]
    #[ensures(stack_own(stack, (*stack).head))]
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        let result = get_nodes_sum((*stack).head);

        result
    }
}