#[predicate]
pub fn Stack(node: *mut Node) = (*node).next |-> ?next &*& 
    match next {
        std::ptr::null_mut() => emp,
        _ => Stack(next),
    };

#[predicate]
pub fn stack_pred(stack: *mut Stack) = (*stack).head |-> ?head &*& 
    match head {
        std::ptr::null_mut() => emp,
        _ => Stack(head),
    };

unsafe fn stack_get_count(stack: *mut Stack) -> i32
{
    #[requires(stack_pred(stack))]
    #[ensures(stack_pred(stack) &*& result >= 0)]
    let mut n = (*stack).head;
    let mut i = 0;
    #[invariant(n |-> ?n_next &*& 
                match n {
                    std::ptr::null_mut() => emp,
                    _ => Stack(n),
                } &*& 
                stack_pred(stack) &*& 
                i >= 0)]
    loop {
        if n.is_null() {
            break;
        }
        n = (*n).next;
        i += 1;
    }

    i
}