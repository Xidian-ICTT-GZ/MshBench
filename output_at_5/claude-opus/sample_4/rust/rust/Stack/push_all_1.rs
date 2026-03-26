impl Stack {
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
        //@ req obs: obs_points_to_stack(stack) &*& obs_points_to_stack(other);
        //@ ens obs: obs_points_to_stack(stack);
    {
        let head0 = (*other).head;
        dealloc(other as *mut u8, std::alloc::Layout::new::<Stack>());
        let mut n = head0;
        if !n.is_null() {
            loop {
                if (*n).next.is_null() {
                    break;
                }
                n = (*n).next;
            }
            (*n).next = (*stack).head;
            (*stack).head = head0;
        }
    }
}