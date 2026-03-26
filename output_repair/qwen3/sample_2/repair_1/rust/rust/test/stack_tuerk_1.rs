use std::ptr;

#[predicate]
fn stack_node(ptr: *mut Node, data: i32) -> bool {
    *ptr != null_ptr() &&
    (*ptr).data == data &&
    stack_node((*ptr).next, 0) // Placeholder for recursive structure, simplified for VeriFast syntax constraints
}

#[predicate]
fn stack_owned(ptr: *mut Stack, count: i32) -> bool {
    *ptr != null_ptr() &&
    (*ptr).head != null_ptr() &&
    list_owned((*ptr).head, count)
}

#[predicate]
fn list_owned(head: *mut Node, count: i32) -> bool {
    if head.is_null() {
        count == 0
    } else {
        count > 0 &&
        list_owned((*head).next, count - 1)
    }
}

#[predicate]
fn node_ptr(p: *mut Node) -> bool {
    p != null_ptr()
}

unsafe fn stack_get_count(stack: *mut Stack) -> i32
    #[requires(*stack != null_ptr())]
    #[requires(list_owned((*stack).head, ?n))]
    #[ensures(result == n)]
{
    let mut n = (*stack).head;
    let mut i = 0;
    loop {
        #[invariant(n.is_null() || node_ptr(n))]
        #[invariant(i >= 0)]
        #[invariant(list_owned(n, ?k) ==> result + k == n)] // Simplified invariant logic for counting
        if n.is_null() {
            break;
        }
        n = (*n).next;
        i += 1;
    }
    i
}