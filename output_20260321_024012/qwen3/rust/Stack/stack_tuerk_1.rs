//@ pred Stack(node: *mut Node;) = node == 0i32 || 
//@   node |-> ?next &*& Stack(next);
//@ 
//@ pred Stack_struct(stack: *mut Stack;) = stack |-> ?head &*& Stack(head);

unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ req Stack_struct(stack);
//@ ens Stack_struct(stack) &*& result >= 0;
{
    let mut n = (*stack).head;
    //@ open Stack_struct(stack);
    //@ close Stack_struct(stack);
    let mut i = 0;
    loop {
        //@ open Stack(n);
        if n.is_null() {
            //@ close Stack(n);
            break;
        }
        n = (*n).next;
        i += 1;
        //@ close Stack(n);
    }

    i
}