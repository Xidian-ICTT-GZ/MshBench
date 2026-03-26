use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

verus! {

predicate node_list(ptr: *mut Node) {
    if ptr.is_null() {
        true
    } else {
        let n = unsafe { &*ptr };
        sep(
            node(ptr),
            node_list(n.next)
        )
    }
}

predicate node(ptr: *mut Node) {
    !ptr.is_null()
}

} // verus!

#[verifier::external_body]
#[requires(n != null_mut() && sep(node_list(*n), true))]
#[ensures(node_list(*n))]
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