#[predicate]
fn stack_node(node: *mut Node) -> bool;

#[predicate]
fn stack(stack: *mut Stack, head: *mut Node) -> bool;

unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    #[requires(stack(stack, ?head) && stack_nodes(head))]
    #[ensures(stack(stack, head) && stack_nodes(head) && result == count_nodes(head))]
    let mut n = (*stack).head;
    let mut i = 0;
    #[invariant(stack(stack, ?s_head) && stack_nodes(n) && i == count_from_to(s_head, n))]
    loop {
        if n.is_null() {
            break;
        }
        n = (*n).next;
        i += 1;
    }

    i
}

#[predicate]
fn stack_nodes(node: *mut Node) -> bool {
    if node.is_null() {
        true
    } else {
        stack_node(node) && stack_nodes((*node).next)
    }
}

#[pure]
fn count_nodes(node: *mut Node) -> i32 {
    if node.is_null() {
        0
    } else {
        1 + count_nodes((*node).next)
    }
}

#[pure]
fn count_from_to(start: *mut Node, end: *mut Node) -> i32 {
    if start == end {
        0
    } else if start.is_null() {
        0
    } else {
        1 + count_from_to((*start).next, end)
    }
}