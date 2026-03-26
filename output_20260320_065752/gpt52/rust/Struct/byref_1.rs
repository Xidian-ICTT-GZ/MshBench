use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

/*@

pred nodes_list(n: *mut Node) =
    if n == 0 as *mut Node {
        emp
    } else {
        alloc_block_Node(n) &*&
        n.value |-> ?v &*&
        n.next |-> ?next &*&
        nodes_list(next)
    };

@*/

//@ req n != null_mut() &*& nodes_list(*n);
//@ ens nodes_list(*n);
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
{
    //@ open nodes_list(*n);
    if !(*n).is_null() {
        let node = *n;

        let keep = p((*node).value);
        if keep {
            let next_ptr = &mut (*node).next;
            //@ open nodes_list((*node).next);
            filter_nodes(next_ptr, p);
            //@ close nodes_list((*node).next);
            //@ close nodes_list(node);
        } else {
            let next_ = (*node).next;
            //@ open nodes_list(next_);
            dealloc(node as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
            //@ close nodes_list(*n);
        }
    } else {
        //@ close nodes_list(*n);
    }
}