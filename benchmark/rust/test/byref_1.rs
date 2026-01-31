use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
    //@ req *n |-> ?node &*& Nodes(node, _) &*& [_]is_I32Predicate(p);
    //@ ens *n |-> ?node0 &*& Nodes(node0, _);
{
    if !(*n).is_null() {
        let node = *n;
        //@ open Nodes(node, _);
        let keep = p((*node).value);
        if keep {
            let next_ptr = &mut (*node).next;
            filter_nodes(next_ptr, p);
            //@ close Nodes(node, ?count);
        } else {
            let next_ = (*node).next;
            dealloc(node as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
        }
    }
}
