use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

#[predicate]
fn node_list(ptr: *mut Node) -> bool {
    match ptr.is_null() {
        true => true,
        false => node_owned(ptr),
    }
}

#[predicate]
fn node_owned(ptr: *mut Node) -> bool {
    !ptr.is_null() && sep!(
        ptr as *mut u8 |-> _,
        node_list(unsafe { (*ptr).next })
    )
}

#[requires(!n.is_null())]
#[requires(sep!(n |-> old_n, node_list(old_n)))]
#[ensures(sep!(n |-> result_n, node_list(result_n)))]
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