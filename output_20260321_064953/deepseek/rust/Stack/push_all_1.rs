// verifast_options{}

impl Stack {
unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
//@ req ptr::nonnull(stack) &*& stack->head |-> ?head &*& ptr::nonnull(other) &*& other->head |-> ?other_head &*& lseg(other_head, 0, ?vs);
//@ ens ptr::nonnull(stack) &*& stack->head |-> ?new_head &*& lseg(new_head, 0, ?vs2) &*& vs2 == append(vs_old, vs);
{
    //@ open lseg(other_head, 0, vs);
    let head0 = (*other).head;
    //@ close lseg(head0, 0, vs);
    dealloc(other as *mut u8, Layout::new::<Stack>());
    let mut n = head0;

    if !n.is_null() {
        //@ open lseg(head0, 0, vs);
        //@ assert lseg(head0, 0, vs) == lseg(head0, ?next, ?v) &*& node(next, ?v2, ?tail);
        loop {
            //@ open lseg(n, 0, _);
            //@ open node(n, _, _);
            if (*n).next.is_null() {
                //@ close node(n, _, _);
                //@ close lseg(n, 0, _);
                break;
            }
            n = (*n).next;
            //@ close lseg(old_n, 0, _);
        }
        //@ open lseg(n, 0, _);
        //@ open node(n, _, _);
        (*n).next = (*stack).head;
        //@ close node(n, _, _);
        //@ close lseg(n, 0, _);
        //@ close lseg(head0, 0, _);
        (*stack).head = head0;
        //@ close lseg(head0, 0, _);
    }
    //@ close lseg(head0, 0, _);
}
}