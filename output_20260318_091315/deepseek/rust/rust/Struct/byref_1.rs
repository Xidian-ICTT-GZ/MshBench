use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

#[predicate]
fn node_own(n: *mut Node, v: i32, next: *mut Node) -> bool {
    struct Node { value: i32, next: *mut Node }(n) &*& (*n).value == v &*& (*n).next == next
}

#[predicate]
fn nodes(n: *mut Node) -> bool {
    n == null_mut() ? true : 
        exists::<i32, *mut Node>(|v, next| node_own(n, v, next) &*& nodes(next))
}

#[predicate]
fn nodes_pred(n: *mut Node, p: I32Predicate) -> bool {
    n == null_mut() ? true : 
        exists::<i32, *mut Node>(|v, next| 
            node_own(n, v, next) &*& 
            nodes_pred(next, p) &*&
            p(v) == true
        )
}

#[requires(nodes(*n))]
#[ensures(nodes_pred(*n, p))]
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