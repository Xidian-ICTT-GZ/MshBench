use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

/*@
pred node(n: *mut Node; value: i32, next: *mut Node) =
    alloc_block(n, std::mem::size_of::<Node>()) &*&
    struct_Node_padding(n) &*&
    (*n).value |-> value &*&
    (*n).next |-> next;
@*/

type I32Predicate = fn(i32) -> bool;

//@ req (*n).is_null() ? true : node(*n, _, _);
//@ ens (*n).is_null() ? true : node(*n, _, _);
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
{
    if !(*n).is_null() {
        let node = *n;
        //@ open node(node, _, _);
        
        let keep = p((*node).value);
        if keep {
            let next_ptr = &mut (*node).next;
            filter_nodes(next_ptr, p);
            //@ close node(node, _, _);
        } else {
            let next_ = (*node).next;
            //@ close node(node, _, _);
            dealloc(node as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
        }
    }
}