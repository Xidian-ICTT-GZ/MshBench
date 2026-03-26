use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

predicate node_list(*mut Node ptr;);

predicate node_owned(*mut Node ptr) =
    ptr != null_mut::<Node>() &&
    std::alloc::alloc_block(ptr as *mut u8, Layout::new::<Node>()) *
    node_list((*ptr).next);

predicate node_list(*mut Node ptr) =
    ptr == null_mut::<Node>() ||
    node_owned(ptr);

#[requires(n != null_mut())]
#[requires(node_list(*n))]
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
            #[ensures(std::alloc::dealloc_block(node as *mut u8, Layout::new::<Node>()))]
            {
                dealloc(node as *mut u8, Layout::new::<Node>());
            }
            *n = next_;
            filter_nodes(n, p);
        }
    }
}