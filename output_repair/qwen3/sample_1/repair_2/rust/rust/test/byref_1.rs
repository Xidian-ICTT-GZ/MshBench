use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

#[verifast::predicate]
fn node_list(ptr: *mut Node) -> bool {
    match ptr as usize {
        0 => true,
        _ => verifast::sep![
            ptr |-> struct Node { value: _, next: (*ptr).next },
            node_list((*ptr).next)
        ]
    }
}

#[verifast::requires(n != null_mut() && verifast::sep![n |-> *n, node_list(*n)])]
#[verifast::ensures(verifast::sep![n |-> *n, node_list(*n)])]
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