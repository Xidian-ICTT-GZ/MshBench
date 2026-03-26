use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

/*@
predicate nodes(n: *mut Node) =
    n == null_mut() ?
        true
    :
        alloc_block(n, std::mem::size_of::<Node>()) &*&
        struct_Node_padding(n) &*&
        (*n).value |-> _ &*&
        (*n).next |-> ?next &*&
        nodes(next);
@*/

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
    //@ req nodes(*n);
    //@ ens nodes(*n);
{
    //@ open nodes(*n);
    if !(*n).is_null() {
        let node = *n;
        //@ open nodes(node);
        
        let keep = p((*node).value);
        if keep {
            let next_ptr = &mut (*node).next;
            filter_nodes(next_ptr, p);
            //@ close nodes(node);
        } else {
            let next_ = (*node).next;
            //@ close nodes(node);
            dealloc(node as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
        }
    }
    //@ close nodes(*n);
}