use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

/*@

pred nodes(ptr: *mut Node) =
    ptr == null_mut() ?
        true
    :
        std::alloc::alloc_block(ptr as *mut u8, Layout::new::<Node>()) &*&
        std::ptr::writeable(ptr, std::mem::size_of::<Node>()) &*&
        (*ptr).value |-> ?v &*&
        (*ptr).next |-> ?nxt &*&
        nodes(nxt);

pred nodes_ptr(pp: *mut *mut Node) =
    *pp |-> ?p &*& nodes(p);

@*/

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
    //@ req nodes_ptr(n);
    //@ ens nodes_ptr(n);
{
    //@ open nodes_ptr(n);
    if !(*n).is_null() {
        let node = *n;

        //@ open nodes(node);
        let keep = p((*node).value);
        if keep {
            let next_ptr = &mut (*node).next;
            //@ close nodes(node);
            filter_nodes(next_ptr, p);
            //@ open nodes_ptr(next_ptr);
            //@ open nodes(node);
            //@ close nodes(node);
            //@ close nodes_ptr(n);
        } else {
            let next_ = (*node).next;
            //@ open nodes(next_);
            //@ close nodes(next_);
            dealloc(node as *mut u8, Layout::new::<Node>());
            //@ close nodes(next_);
            *n = next_;
            //@ close nodes_ptr(n);
            filter_nodes(n, p);
        }
    } else {
        //@ close nodes(*n);
        //@ close nodes_ptr(n);
    }
}