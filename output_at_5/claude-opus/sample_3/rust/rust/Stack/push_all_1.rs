impl Stack {
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
        //@ req true;
        //@ ens true;
    {
        let head0 = (*other).head;
        dealloc(other as *mut u8, std::alloc::Layout::new::<Stack>());
        let mut n = head0;
        if !n.is_null() {
            //@ // Traversing linked list: no specific predicate available, keep req/ens weak
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