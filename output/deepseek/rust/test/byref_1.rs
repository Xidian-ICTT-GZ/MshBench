use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

predicate node(n: *mut Node; value: i32, next: *mut Node) {
    struct_Node_padding(n) &*& (*n).value |-> value &*& (*n).next |-> next;
}

predicate lseg(start: *mut Node, end: *mut Node; list: seq<i32>) {
    start == end ? list == seq!{} :
    node(start, head_val, next) &*& lseg(next, end, tail) &*& list == seq![head_val] + tail;
}

type I32Predicate = fn(i32) -> bool;

#[requires(lseg(n, null_mut(), list))]
#[ensures(lseg(result, null_mut(), filtered_list) &*& filtered_list == list.filter(|&x| p(x)))]
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate) {
    if !(*n).is_null() {
        let node_ptr = *n;
        #[invariant(lseg(node_ptr, null_mut(), tail) &*& lseg(*n, node_ptr, prefix) &*& *n |-> node_ptr)]
        {
            let keep = p((*node_ptr).value);
            if keep {
                let next_ptr = &mut (*node_ptr).next;
                filter_nodes(next_ptr, p);
            } else {
                let next_ = (*node_ptr).next;
                dealloc(node_ptr as *mut u8, Layout::new::<Node>());
                *n = next_;
                filter_nodes(n, p);
            }
        }
    }
}