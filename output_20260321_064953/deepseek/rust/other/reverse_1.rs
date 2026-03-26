struct Node {
    next: *mut Node,
}

//@ predicate nodes(n: *mut Node; count: usize) = 
//@     if n.is_null() { count == 0 } else { 
//@         struct_Node_padding(n) &*& 
//@         (*n).next |-> ?next &*& 
//@         nodes(next, ?c) &*& 
//@         count == c + 1 
//@     };

impl Node {

    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node
    //@ req nodes(n, ?cnt);
    //@ ens nodes(result, cnt);
    {
        let mut m = std::ptr::null_mut();
        //@ close nodes(null_mut(), 0);
        loop {
            //@ open nodes(n, _);
            if n.is_null() {
                //@ open nodes(null_mut(), _);
                return m;
            }
            let k = (*n).next;
            //@ open nodes(k, _);
            (*n).next = m;
            m = n;
            n = k;
            //@ close nodes(m, _);
        }
    }

}