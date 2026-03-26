use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

#[predicate]
fn node_own(n: *mut Node, value: i32, next: *mut Node) -> bool {
    struct_own!{n => Node { value, next }}
}

#[predicate]
fn nodes(n: *mut Node) -> bool {
    if n.is_null() {
        emp
    } else {
        exists!(let value = ?; let next = ?;
            node_own(n, value, next) * nodes(next))
    }
}

#[predicate]
fn nodes_mut(n: *mut *mut Node) -> bool {
    exists!(let head = ?; nodes(head) * struct_own!{n => head})
}

#[requires(nodes_mut(n))]
#[ensures(nodes_mut(n))]
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate) {
    if !(*n).is_null() {
        let node = *n;
        
        #[invariant(nodes_mut(n))]
        {
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
}