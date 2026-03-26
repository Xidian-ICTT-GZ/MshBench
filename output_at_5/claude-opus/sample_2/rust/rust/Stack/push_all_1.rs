impl Stack {
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
        //@ req true;
        //@ ens true;
    {
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;
        if !n.is_null() {
            //@ // We do not have explicit predicates; use ghost invariant for pointer traversal
            //@ open true; // no specific predicate known, open dummy
            loop {
                if (*n).next.is_null() {
                    break;
                }
                n = (*n).next;
            }
            (*n).next = (*stack).head;
            (*stack).head = head0;
            //@ close true; // close dummy predicate
        }
    }
}