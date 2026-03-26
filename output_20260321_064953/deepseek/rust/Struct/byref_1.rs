use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
    //@ req ptr(n, _) &*& struct_Node_padding(_);
    //@ ens ptr(n, _) &*& struct_Node_padding(_);
{
    //@ open ptr(n, _);
    //@ open struct_Node_padding(_);
    if !(*n).is_null() {
        let node = *n;
        
        let keep = p((*node).value);
        if keep {
            let next_ptr = &mut (*node).next;
            filter_nodes(next_ptr, p);
            
        } else {
            let next_ = (*node).next;
            dealloc(node as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
        }
    }
    //@ close ptr(n, _);
    //@ close struct_Node_padding(_);
}