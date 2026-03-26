unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ req ptr::<Stack>(stack, ?stack_p);
//@ ens ptr::<Stack>(stack, stack_p) &*& result >= 0;
{
    //@ open ptr::<Stack>(stack, stack_p);
    let mut n = (*stack).head;
    let mut i = 0;
    loop
    //@ inv ptr::<Stack>(stack, stack_p) &*& i >= 0;
    {
        if n.is_null() {
            //@ close ptr::<Stack>(stack, stack_p);
            break;
        }
        //@ open ptr::<Node>(n, ?node_p);
        n = (*n).next;
        i += 1;
        //@ close ptr::<Stack>(stack, stack_p);
    }
    i
}