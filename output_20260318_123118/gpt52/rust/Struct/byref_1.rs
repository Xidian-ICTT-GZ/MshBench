use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

/*@

predicate nodes_(ptr: *mut Node; vs: list<i32>) =
    ptr == 0 ?
        vs == nil
    :
        struct_Node(ptr, ?v, ?next) &*& nodes_(next, ?vs0) &*& vs == cons(v, vs0);

predicate nodes_handle(npp: *mut *mut Node; vs: list<i32>) =
    pointer(npp, ?p) &*& nodes_(p, vs);

@*/

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
    //@ requires nodes_handle(n, ?vs);
    //@ ensures nodes_handle(n, ?vs2);
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