impl Stack {
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
        //@ req stack.ptr(?stack_inv) &*& other.ptr(?other_inv);
        //@ ens stack.ptr(?stack_inv2);
    {
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;
        if !n.is_null() {
            loop {
                //@ open stack_inv();
                if (*n).next.is_null() {
                    break;
                }
                n = (*n).next;
                //@ close stack_inv();
            }
            (*n).next = (*stack).head;
            (*stack).head = head0;
        }
    }
}