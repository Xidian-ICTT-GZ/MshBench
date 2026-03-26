use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

/*@
predicate node_list(ptr: *mut Node) =
    ptr as usize == 0 ? emp : node_owned(ptr);

predicate node_owned(ptr: *mut Node) =
    ptr as usize != 0 && Owned(ptr, Node { value: _, next: _ });
@*/

/*@
requires n != null_mut() && Owned(n, _) && node_owned(*n);
ensures n != null_mut() && Owned(n, _) && node_list(*n);
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