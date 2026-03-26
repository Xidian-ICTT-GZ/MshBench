unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    #[requires(stack != std::ptr::null_mut())]
    #[requires(stack_inv(stack))]
    #[ensures(result >= 0)]
    #[ensures(stack_inv(stack))]
    let mut n = (*stack).head;
    let mut i = 0;
    #[invariant(stack_inv(stack))]
    #[invariant(n == (*stack).head || list_segment((*stack).head, n, i))]
    #[invariant(i >= 0)]
    loop {
        if n.is_null() {
            break;
        }
        #[requires(!n.is_null())]
        #[requires(list_node(n))]
        #[ensures(list_node(old(n)))]
        #[ensures(result == (*old(n)).next)]
        let next = (*n).next;
        n = next;
        i += 1;
    }

    i
}

#[predicate]
fn stack_inv(stack: *mut Stack) -> bool {
    exists<list: *mut Node> (*stack).head == list && list_inv(list)
}

#[predicate]
fn list_inv(n: *mut Node) -> bool {
    if n.is_null() {
        true
    } else {
        exists<next: *mut Node> (*n).next == next && list_node(n) && list_inv(next)
    }
}

#[predicate]
fn list_node(n: *mut Node) -> bool {
    exists<next: *mut Node> (*n).next == next && true
}

#[predicate]
fn list_segment(start: *mut Node, end: *mut Node, len: i32) -> bool {
    if start == end {
        len == 0
    } else {
        exists<next: *mut Node> (*start).next == next && list_node(start) && 
            list_segment(next, end, len - 1) && len > 0
    }
}