unsafe fn stack_get_count(stack: *mut Stack) -> i32
    #[requires(stack.is_nonnull())]
    #[requires(stack_ownership(stack))]
    #[ensures(stack_ownership(stack))]
    #[ensures(result >= 0)]
{
    let mut n = (*stack).head;
    let mut i = 0;
    #[invariant(stack.is_nonnull())]
    #[invariant(stack_ownership(stack))]
    #[invariant(n.is_nonnull() ==> node_ownership(n))]
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