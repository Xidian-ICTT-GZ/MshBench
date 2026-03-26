unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    let mut n = (*stack).head;
    let mut i = 0;
    loop {
        if n.is_null() {
            break;
        }
        n = (*n).next;
        i += 1;
    }

    i
}

#[verifast::predicate]
pub fn stack_node(node: *mut StackNode) -> bool {
    node != std::ptr::null_mut()
}

#[verifast::predicate]
pub fn stack(stack_ptr: *mut Stack, head: *mut StackNode) -> bool {
    stack_ptr != std::ptr::null_mut() && (*stack_ptr).head == head
}

#[verifast::predicate]
pub fn stack_nodes(node: *mut StackNode, tail: *mut StackNode) -> bool {
    if node.is_null() {
        tail.is_null()
    } else {
        stack_node(node) && verifast::points_to((*node).next, ?next) && stack_nodes(next, tail)
    }
}

#[verifast::pure]
pub fn stack_length(node: *mut StackNode) -> i32 {
    if node.is_null() {
        0
    } else {
        1 + stack_length(unsafe { (*node).next })
    }
}

unsafe fn stack_get_count_specified(stack: *mut Stack) -> i32 {
    #[verifast::requires(stack(stack, ?head) && stack_nodes(head, std::ptr::null_mut()))]
    #[verifast::ensures(stack(stack, head) && stack_nodes(head, std::ptr::null_mut()) && result == stack_length(head))]
    {
        let mut n = (*stack).head;
        let mut i = 0;
        #[verifast::invariant(stack(stack, ?s_head) && stack_nodes(n, ?current_tail) && stack_nodes(current_tail, std::ptr::null_mut()) && i + stack_length(current_tail) == stack_length(s_head))]
        loop {
            if n.is_null() {
                break;
            }
            let next = (*n).next;
            verifast::consume(stack_nodes(n, current_tail));
            verifast::produce(stack_node(n));
            verifast::produce(verifast::points_to((*n).next, next));
            verifast::consume(stack_nodes(next, current_tail));
            n = next;
            i += 1;
        }

        i
    }
}