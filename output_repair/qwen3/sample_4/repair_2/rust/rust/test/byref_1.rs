use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

#[verifast::predicate]
pub fn node_list(ptr: *mut Node) -> bool {
    match ptr.is_null() {
        true => verifast::sep_true(),
        false => node_owned(ptr),
    }
}

#[verifast::predicate]
pub fn node_owned(ptr: *mut Node) -> bool {
    !ptr.is_null() && verifast::sep!(
        verifast::points_to(ptr as *mut u8, _),
        node_list(unsafe { (*ptr).next })
    )
}

#[verifast::requires(!n.is_null())]
#[verifast::requires(verifast::sep!(verifast::points_to(n, old_n), node_list(old_n)))]
#[verifast::ensures(verifast::sep!(verifast::points_to(n, result_n), node_list(result_n)))]
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