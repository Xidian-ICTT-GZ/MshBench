use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

/*@

pred nodes(list: *mut Node) =
    if list == null_mut() {
        true
    } else {
        (*list).value |-> ?v &*&
        (*list).next |-> ?nxt &*&
        std::alloc::alloc_block(list as *mut u8, Layout::new::<Node>()) &*&
        nodes(nxt)
    };

@*/

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
    //@ req n |-> ?head &*& nodes(head);
    //@ ens n |-> ?head2 &*& nodes(head2);
{
    if !(*n).is_null() {
        let node = *n;

        let keep = p((*node).value);
        if keep {
            //@ open nodes(node);
            let next_ptr = &mut (*node).next;
            filter_nodes(next_ptr, p);
            //@ close nodes(node);
        } else {
            //@ open nodes(node);
            let next_ = (*node).next;
            dealloc(node as *mut u8, Layout::new::<Node>());
            //@ open std::alloc::alloc_block(node as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
        }
    }
}