// verifast_options{}

impl Stack {
unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
//@ req ptr::nonnull(stack) &*& stack.own_stack() &*& ptr::nonnull(other) &*& other.own_stack();
//@ ens ptr::nonnull(stack) &*& stack.own_stack();
{
    //@ open stack.own_stack();
    //@ open other.own_stack();
    let head0 = (*other).head;
    //@ close other.own_nodes(head0);
    //@ close other.own_stack();
    //@ open other.own_stack();
    dealloc(other as *mut u8, Layout::new::<Stack>());
    let mut n = head0;

    if !n.is_null() {
        //@ open nodes(n, _);
        loop {
            //@ open nodes(n, _);
            if (*n).next.is_null() {
                //@ close nodes(n, _);
                break;
            }
            n = (*n).next;
            //@ close nodes(n, _);
        }
        //@ open nodes(n, _);
        (*n).next = (*stack).head;
        //@ close nodes(n, _);
        //@ close nodes(head0, _);
        (*stack).head = head0;
        //@ close stack.own_stack();
    } else {
        //@ close stack.own_stack();
    }
}
}