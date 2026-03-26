#![allow(dead_code)]

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
        _ => len > 0 && n != std::ptr::null_mut() && 
             exists(|next: *mut Node| 
             unsafe { (*n).next == next } && node_list(next, len - 1))
    }
}

#[predicate]
fn stack(s: *mut Stack, len: i32) -> bool {
    s != std::ptr::null_mut() && exists(|head: *mut Node|
    unsafe { (*s).head == head } && node_list(head, len))
}

#[requires(stack(stack, ?len))]
#[ensures(stack(stack, len))]
unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    let mut n = (*stack).head;
    let mut i = 0;
    loop {
        #[invariant(i >= 0 && node_list(n, ?remaining) && i + remaining == ?len)]
        if n.is_null() {
            break;
        }
        n = (*n).next;
        i += 1;
    }

    i
}