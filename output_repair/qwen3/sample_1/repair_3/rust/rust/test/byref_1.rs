use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

predicate node_list(ptr: *mut Node) = 
    ptr == null_mut() ?
        true
    :
        ptr |-> struct Node { value: _, next: (*ptr).next } &*& node_list((*ptr).next);

predicate node_ptr_ref(ptr: *mut *mut Node, v: *mut Node) = 
    ptr |-> v &*& node_list(v);

#[requires(node_ptr_ref(n, ?old_head))]
#[ensures(node_ptr_ref(n, ?new_head))]
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate) {
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
}