struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate node_list(n: *mut Node, len: i32) =
    match len {
        0 => n.is_null(),
        _ => n != null && exists<*mut Node>(next => 
            (*n).next == next && node_list(next, len - 1)
        )
    };

predicate stack(s: *mut Stack, len: i32) =
    s != null && exists<*mut Node>(head => 
        (*s).head == head && node_list(head, len)
    );

#[requires(stack(stack, len) & len >= 0)]
#[ensures(stack(stack, len) & result == len)]
unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    let mut n = (*stack).head;
    let mut i = 0;
    loop {
        #[invariant(node_list(n, len - i) & i >= 0 & i <= len)]
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