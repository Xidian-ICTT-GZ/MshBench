unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ req stack != 0 &*& alloc_block_stack(stack, _) &*& (*stack).head |-> ?head;
//@ ens alloc_block_stack(stack, _) &*& (*stack).head |-> head &*& result >= 0;
{
    let mut n = (*stack).head;
    let mut i = 0;
    //@ inv list_segment(n, ?tail) &*& i >= 0 &*& (tail == 0 ? true : alloc_block_node(tail, _)) &*& (*stack).head |-> head;
    loop {
        if n.is_null() {
            break;
        }
        //@ open alloc_block_node(n, _);
        //@ open node_next(n, _);
        //@ open node_value(n, _);
        n = (*n).next;
        i += 1;
        //@ close list_segment(n, tail);
    }
    i
}