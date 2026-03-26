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
        node_ptr(head) &&
        list_owned((*head).next, count - 1)
    }
}

#[predicate]
fn node_ptr(p: *mut Node) -> bool {
    p != ptr::null_mut()
}

#[predicate]
fn stack_owned(ptr: *mut Stack, count: i32) -> bool {
    ptr != ptr::null_mut() &&
    list_owned((*ptr).head, count)
}

unsafe fn stack_get_count(stack: *mut Stack) -> i32
requires
    stack != ptr::null_mut(),
    list_owned((*stack).head, ?n)
ensures
    result == n
{
    let mut n = (*stack).head;
    let mut i = 0;
    loop
        invariant
            n.is_null() || node_ptr(n),
            i >= 0,
            list_owned(n, ?k),
            i + k == n
    {
        if n.is_null() {
            break;
        }
        n = (*n).next;
        i += 1;
    }
    i
}