#[predicate]
pub fn stack_node(node: *mut Node) = (*node).next |-> ?next &*& node != std::ptr::null_mut() &*&
    if next == std::ptr::null_mut() {
        true
    } else {
        stack_node(next)
    };

#[predicate]
pub fn stack(stack: *mut Stack) = (*stack).head |-> ?head &*& stack != std::ptr::null_mut() &*&
    if head == std::ptr::null_mut() {
        true
    } else {
        stack_node(head)
    };

unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    #[requires(stack(stack))]
    #[ensures(stack(stack) &*& result >= 0)]
    let mut n = (*stack).head;
    let mut i = 0;
    #[invariant(n == std::ptr::null_mut() || stack_node(n))]
    #[invariant(i >= 0)]
    loop {
        if n.is_null() {
            break;
        }
        n = (*n).next;
        i += 1;
    }

    i
}