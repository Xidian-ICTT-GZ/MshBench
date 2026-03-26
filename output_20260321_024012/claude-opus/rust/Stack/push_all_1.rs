impl Stack {
//@ pred stack(self: *mut Stack, head: *mut Node) = self->Stack { head: head };
//@ pred node(n: *mut Node, next: *mut Node) = n->Node { next: next };
unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
//@ requires stack(?s) &*& other(?o) &*& stack(stack, ?shead) &*& stack(other, ?ohead);
//@ ensures stack(stack, ?reshead) &*& stack(other, null());
{
    let head0 = (*other).head;
    //@ open stack(other, ohead);
    dealloc(other as *mut u8, Layout::new::<Stack>());
    let mut n = head0;
    if !n.is_null() {
        loop {
            //@ if n.is_null() { open node(n, _); assert false; }
            //@ open node(n, (*n).next);
            if (*n).next.is_null() {
                //@ close node(n, (*n).next);
                break;
            }
            n = (*n).next;
        }
        //@ open node(n, (*n).next);
        (*n).next = (*stack).head;
        //@ close node(n, (*n).next);
        (*stack).head = head0;
        //@ close stack(stack, head0);
    } else {
        //@ close stack(stack, shead);
    }
    //@ close stack(other, null());
}
}