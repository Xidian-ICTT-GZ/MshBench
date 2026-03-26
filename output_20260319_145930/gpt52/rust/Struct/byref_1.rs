use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

/*@

pred nodes_list(n: *mut Node) =
    n == null_mut() ?
        true
    :
        alloc_block_Node(n) &*&
        (*n).value |-> ?v &*&
        (*n).next |-> ?nx &*&
        nodes_list(nx);

pred nodes_list_ptr(pp: *mut *mut Node) =
    pp != null_mut() &*& *pp |-> ?n &*& nodes_list(n);

@*/

//@ req nodes_list_ptr(n);
//@ ens nodes_list_ptr(n);
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
{
    //@ open nodes_list_ptr(n);
    if !(*n).is_null() {
        let node = *n;
        //@ open nodes_list(node);

        let keep = p((*node).value);
        if keep {
            let next_ptr = &mut (*node).next;
            //@ close nodes_list(node);
            //@ open nodes_list_ptr(next_ptr);
            filter_nodes(next_ptr, p);
            //@ close nodes_list_ptr(next_ptr);
            //@ open nodes_list_ptr(next_ptr);
            //@ open nodes_list((*next_ptr));
            //@ close nodes_list((*next_ptr));
            //@ close nodes_list(node);
        } else {
            let next_ = (*node).next;
            //@ close nodes_list(next_);
            dealloc(node as *mut u8, Layout::new::<Node>());
            *n = next_;
            //@ close nodes_list_ptr(n);
            filter_nodes(n, p);
            return;
        }
        //@ close nodes_list_ptr(n);
    } else {
        //@ close nodes_list_ptr(n);
    }
}