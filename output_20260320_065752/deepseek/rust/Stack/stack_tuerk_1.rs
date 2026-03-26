unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ req stack != 0 &*& alloc_block_stack(stack, _) &*& (*stack).head |-> ?head &*& lseg(head, 0, _);
//@ ens alloc_block_stack(stack, _) &*& (*stack).head |-> head &*& lseg(head, 0, _) &*& result >= 0;
{
    let mut n = (*stack).head;
    let mut i = 0;
    //@ open lseg(head, 0, _);
    //@ close lseg(head, 0, _);
    loop
    //@ inv lseg(n, 0, ?vs) &*& i >= 0 &*& i + length(vs) == length(?orig_vs);
    {
        if n.is_null() {
            //@ open lseg(0, 0, _);
            break;
        }
        //@ open lseg(n, 0, _);
        //@ assert alloc_block_node(n, _) &*& (*n).next |-> ?next &*& (*n).value |-> _;
        n = (*n).next;
        i += 1;
        //@ close lseg(n, 0, _);
    }
    i
}