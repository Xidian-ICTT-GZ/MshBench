use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

/*@
predicate_family node_list(ptr: *mut Node);

lemma void node_list_null()
    requires true;
    ensures node_list(null_mut());
{
}

lemma void node_list_cons(node: *mut Node, next: *mut Node)
    requires node != null_mut() && node_list(next);
    ensures node_list(node);
{
}
@*/

/*@
requires n != null_mut() && node_list(*n);
ensures node_list(*n);
@*/
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