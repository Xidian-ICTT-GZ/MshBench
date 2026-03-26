struct Node {
    next: *mut Node,
}

/*@
pred_ctor node(next: *mut Node)() = 
    alloc_block(next, std::mem::size_of::<Node>()) &*&
    struct_Node_padding(next) &*&
    (*next).next |-> ?next_next;
@*/

impl Node {

    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node
    //@ req node(n)() &*& n != 0 ? true : emp;
    //@ ens node(result)() &*& result != 0 ? true : emp;
    {
        let mut m = std::ptr::null_mut();
        //@ close node(0)();
        loop {
            //@ inv node(n)() &*& node(m)();
            if n.is_null() {
                //@ open node(0)();
                return m;
            }
            let k = (*n).next;
            //@ open node(n)();
            (*n).next = m;
            //@ close node(n)();
            m = n;
            n = k;
        }
    }

}