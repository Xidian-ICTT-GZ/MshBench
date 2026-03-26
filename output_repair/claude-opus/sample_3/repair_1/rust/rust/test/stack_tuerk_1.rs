struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate node_list(n: *mut Node, len: i32) =
    match len {
        0 => n.is_null(),
        _ => n != std::ptr::null_mut() && exists<*mut Node>(next => 
            (*n).next == next && node_list(next, len - 1)
        )
    };

predicate stack_valid(stack: *mut Stack, len: i32) =
    stack != std::ptr::null_mut() && 
    node_list((*stack).head, len);

#[requires(stack_valid(stack, _))]
#[ensures(result >= 0)]
unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    let mut n = (*stack).head;
    let mut i = 0;
    loop {
        #[invariant(i >= 0 && node_list(n, _))]
        {
            if n.is_null() {
                break;
            }
            n = (*n).next;
            i += 1;
        }
    }

    i
}