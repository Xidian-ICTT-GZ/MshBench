unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ req [?q]stack->?s &*& stack_slice(s, ?elems);
//@ ens [q]stack->s &*& stack_slice(s, elems) &*& result == length(elems);
{
    //@ open stack_slice(s, elems);
    let mut n = (*stack).head;
    let mut i = 0;
    //@ let mut elems_remaining = elems;
    loop
    //@ inv [q]stack->s &*& llist(n, elems_remaining) &*& i + length(elems_remaining) == length(elems);
    {
        //@ open llist(_, _);
        if n.is_null() {
            //@ close llist(n, elems_remaining);
            break;
        }
        n = (*n).next;
        i += 1;
        //@ elems_remaining = tail(elems_remaining);
    }
    i
}