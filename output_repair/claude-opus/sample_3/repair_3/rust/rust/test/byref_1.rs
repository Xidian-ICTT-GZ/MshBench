use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

/*@
pred Node_own(node: *mut Node; value: i32, next: *mut Node) =
    (*node).value |-> value &*& (*node).next |-> next &*& struct_Node_padding(node);

pred Nodes(head: *mut Node;) =
    if head == 0 {
        true
    } else {
        Node_own(head, ?value, ?next) &*& malloc_block_Node(head) &*& Nodes(next)
    };

pred ptr_own(p: *mut *mut Node; v: *mut Node) =
    *p |-> v;
@*/

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
//@ req ptr_own(n, ?head) &*& Nodes(head);
//@ ens ptr_own(n, ?new_head) &*& Nodes(new_head);
{
    //@ open ptr_own(n, head);
    if !(*n).is_null() {
        let node = *n;
        //@ open Nodes(node);
        //@ open Node_own(node, ?value, ?next);

        let keep = p((*node).value);
        if keep {
            //@ close Node_own(node, value, next);
            let next_ptr = &mut (*node).next;
            //@ close ptr_own(next_ptr, next);
            filter_nodes(next_ptr, p);
            //@ open ptr_own(next_ptr, ?new_next);
            //@ close Node_own(node, value, new_next);
            //@ close Nodes(node);
            //@ close ptr_own(n, node);
        } else {
            let next_ = (*node).next;
            dealloc(node as *mut u8, Layout::new::<Node>());
            *n = next_;
            //@ close ptr_own(n, next_);
            filter_nodes(n, p);
        }
    } else {
        //@ close Nodes(head);
        //@ close ptr_own(n, head);
    }
}