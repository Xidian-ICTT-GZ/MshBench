use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

/*@

predicate node(n: *mut Node; v: i32, next: *mut Node) =
    n != 0 &*&
    struct_Node_value(n, v) &*&
    struct_Node_next(n, next);

predicate nodes(n: *mut Node) =
    n == 0 ?
        true
    :
        node(n, ?v, ?next) &*& nodes(next);

predicate nodes_handle(npp: *mut *mut Node) =
    npp != 0 &*& pointer(npp, ?head) &*& nodes(head);

@*/

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
    //@ requires nodes_handle(n);
    //@ ensures nodes_handle(n);
{
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