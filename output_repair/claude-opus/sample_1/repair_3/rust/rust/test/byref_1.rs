use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

/*@
pred Nodes(n: *mut Node; count: i32) =
    if n == 0 as *mut Node {
        count == 0
    } else {
        alloc_block(n as *mut u8, std::mem::size_of::<Node>()) &*&
        struct_Node_padding(n) &*&
        (*n).value |-> ?v &*&
        (*n).next |-> ?next &*&
        Nodes(next, ?tail_count) &*&
        count == tail_count + 1
    };

pred Nodes_frac(n: *mut Node;) =
    if n == 0 as *mut Node {
        emp
    } else {
        alloc_block(n as *mut u8, std::mem::size_of::<Node>()) &*&
        struct_Node_padding(n) &*&
        (*n).value |-> ?v &*&
        (*n).next |-> ?next &*&
        Nodes_frac(next)
    };
@*/

/*@
req *n |-> ?head &*& Nodes_frac(head);
ens *n |-> ?new_head &*& Nodes_frac(new_head);
@*/
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate) {
    //@ open Nodes_frac(head);
    if !(*n).is_null() {
        let node = *n;

        let keep = p((*node).value);
        if keep {
            let next_ptr = &mut (*node).next;
            filter_nodes(next_ptr, p);
            //@ close Nodes_frac(node);
        } else {
            let next_ = (*node).next;
            dealloc(node as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);}
    } else {
        //@ close Nodes_frac(0 as *mut Node);
    }
}