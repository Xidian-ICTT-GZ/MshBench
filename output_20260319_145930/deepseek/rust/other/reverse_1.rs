struct Node {
    next: *mut Node,
}

/*@
pred node(n: *mut Node; next: *mut Node) =
    alloc_block(n, std::mem::size_of::<Node>()) &*&
    struct_Node_padding(n) &*&
    (*n).next |-> next;
@*/

impl Node {

    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node
    //@ req node(n, ?next0) &*& lseg(next0, null, ?vs);
    //@ ens lseg(result, null, rev(vs) ++ [n]);
    {
        let mut m = std::ptr::null_mut();
        //@ close lseg(null, null, _);
        loop {
            //@ inv lseg(n, null, ?ns) &*& lseg(m, null, ?ms) &*& node(n, ?next) &*& ns == [n] ++ ?rest &*& rest == ?tail;
            //@ open lseg(n, null, ns);
            
            
            if n.is_null() {
                //@ open lseg(null, null, _);
                return m;
            }
            //@ open node(n, _);
            let k = (*n).next;
            //@ assert node(n, k);
            
            (*n).next = m;
            //@ close node(n, m);
            m = n;
            n = k;
            //@ close lseg(m, null, [m] ++ ms);
        }
    }

}