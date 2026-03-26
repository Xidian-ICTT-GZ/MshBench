struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

#[requires(stack != std::ptr::null_mut())]
#[ensures(result >= 0)]
unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    let mut n = (*stack).head;
    let mut i = 0;
    loop {
        #[invariant(i >= 0)]
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