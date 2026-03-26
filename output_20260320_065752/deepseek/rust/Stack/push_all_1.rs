/*@
pred node(n: *mut Node) = 
    alloc_block(n, std::mem::size_of::<Node>()) &*&
    struct_Node { next: ?next }(n) &*&
    if next.is_null() {
        true
    } else {
        node(next)
    };
@*/

/*@
pred stack(s: *mut Stack) = 
    alloc_block(s, std::mem::size_of::<Stack>()) &*&
    struct_Stack { head: ?head }(s) &*&
    if head.is_null() {
        true
    } else {
        node(head)
    };
@*/

impl Stack {
//@ req stack(stack) &*& stack(other);
//@ ens stack(stack);
unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
{
    //@ open stack(other);
    let head0 = (*other).head;
    //@ close alloc_block(other as *mut u8, Layout::new::<Stack>());
    dealloc(other as *mut u8, Layout::new::<Stack>());
    let mut n = head0;

    if !n.is_null() {
        //@ open node(head0);
        //@ close node(head0);
        loop {
            //@ inv node(n);
            //@ open node(n);
            if (*n).next.is_null() {
                //@ close node(n);
                break;
            }
            n = (*n).next;
            //@ close node(n);
        }
        //@ open stack(stack);
        (*n).next = (*stack).head;
        (*stack).head = head0;
        //@ close stack(stack);
    } else {
        //@ open stack(stack);
        //@ close stack(stack);
    }
}
}