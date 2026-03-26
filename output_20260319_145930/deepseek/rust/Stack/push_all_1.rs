/*@
pred node(n: *mut Node) =
    alloc_block(n, std::mem::size_of::<Node>()) &*&
    struct_Node_padding(n) &*&
    (*n).value |-> ?v &*&
    (*n).next |-> ?next;
@*/

/*@
pred lseg(first: *mut Node, last: *mut Node) =
    first == last ?
        true
    :
        node(first) &*&
        (*first).next |-> ?next &*&
        lseg(next, last);
@*/

/*@
pred stack(stack: *mut Stack) =
    alloc_block(stack, std::mem::size_of::<Stack>()) &*&
    struct_Stack_padding(stack) &*&
    (*stack).head |-> ?head &*&
    lseg(head, std::ptr::null_mut());
@*/

impl Stack {
//@ req stack(stack) &*& stack(other) &*& stack != other;
//@ ens stack(stack);
unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
{
    //@ open stack(other);
    let head0 = (*other).head;
    //@ close lseg(head0, std::ptr::null_mut());
    //@ open lseg(head0, std::ptr::null_mut());
    dealloc(other as *mut u8, Layout::new::<Stack>());
    let mut n = head0;

    if !n.is_null() {
        //@ open node(n);
        //@ close node(n);
        loop {
            //@ inv lseg(head0, n) &*& node(n) &*& (*n).next |-> ?next &*& lseg(next, std::ptr::null_mut());
            if (*n).next.is_null() {
                break;
            }
            //@ open node(n);
            n = (*n).next;
            //@ open node(n);
            //@ close node(n);
        }
        //@ open lseg(head0, n);
        //@ open stack(stack);
        (*n).next = (*stack).head;
        //@ close lseg(head0, std::ptr::null_mut());
        (*stack).head = head0;
        //@ close stack(stack);
    } else {
        //@ open stack(stack);
        //@ close stack(stack);
    }
}
}