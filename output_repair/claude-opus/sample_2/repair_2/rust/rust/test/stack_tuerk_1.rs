struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn node_list(n: *mut Node, len: i32) -> bool {
    match len {
        0 => n.is_null(),
        _ => n != std::ptr::null_mut() && unsafe {
            exists(|next: *mut Node| (*n).next == next && node_list(next, len - 1))
        }
    }
}

#[predicate]
fn stack(s: *mut Stack, len: i32) -> bool {
    s != std::ptr::null_mut() && unsafe {
        exists(|head: *mut Node| (*s).head == head && node_list(head, len))
    }
}

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