#[predicate]
pub pred Stack(node: *mut Node) = (*node).next |-> ?next &*& 
    match next {
        std::ptr::null_mut() => true,
        _ => Stack(next),
    };

#[predicate]
pub pred stack_t(stack: *mut Stack) = (*stack).head |-> ?head &*& 
    match head {
        std::ptr::null_mut() => true,
        _ => Stack(head),
    };

unsafe fn stack_get_count(stack: *mut Stack) -> i32
    requires stack_t(stack);
    ensures stack_t(stack) &*& result >= 0i32;
{
    let mut n = (*stack).head;
    let mut i = 0;
    loop 
        invariant (*stack).head |-> n &*& 
                  match n {
                      std::ptr::null_mut() => true,
                      _ => Stack(n),
                  } &*& i >= 0i32;
    {
        if n.is_null() {
            break;
        }
        n = (*n).next;
        i += 1;
    }

    i
}