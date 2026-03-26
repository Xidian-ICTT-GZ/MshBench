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


use std::ptr;

#[predicate]
fn list_owned(head: *mut Node, count: i32) -> bool {
    if head.is_null() {
        count == 0
    } else {
        count > 0 &&
        node_owned(head) &&
        list_owned((*head).next, count - 1)
    }
}

#[predicate]
fn node_owned(p: *mut Node) -> bool {
    p != ptr::null_mut() && *p |-> ?_
}

#[predicate]
fn stack_owned(ptr: *mut Stack, count: i32) -> bool {
    ptr != ptr::null_mut() &&
    *ptr |-> ?s &&
    list_owned(s.head, count)
}

#[requires(stack != ptr::null_mut())]
#[requires(list_owned((*stack).head, ?n))]
#[ensures(result == n)]
unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    let mut n = (*stack).head;
    let mut i = 0;
    #[invariant(n.is_null() || node_owned(n))]
    #[invariant(i >= 0)]
    #[invariant(list_owned(n, ?k))]
    #[invariant(i + k == n)]
    loop {
        if n.is_null() {
            break;
        }
        n = (*n).next;
        i += 1;
    }
    i
}