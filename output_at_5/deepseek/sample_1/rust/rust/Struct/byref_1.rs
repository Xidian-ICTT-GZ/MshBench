use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
    //@ req node_points_to_opt(n, ?node_opt);
    //@ ens node_points_to_opt(n, ?new_node_opt);
{
    if !(*n).is_null() {
        let node = *n;
        //@ open node(node, ?value, ?next);
        
        let keep = p((*node).value);
        if keep {
            let next_ptr = &mut (*node).next;
            filter_nodes(next_ptr, p);
            //@ close node(node, value, next);
        } else {
            let next_ = (*node).next;
            dealloc(node as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
        }
    }
}

/*@
pred node(node: *mut Node; value: i32, next: *mut Node) = 
    struct_Node_padding(&(*node).value) &*&
    (*node).value |-> value &*&
    (*node).next |-> next;

pred node_points_to_opt(n: *mut *mut Node; node_opt: Option<*mut Node>) =
    n |-> ?node_ptr &*&
    switch node_opt {
        None => node_ptr == null_mut(),
        Some(node) => node(node, ?value, ?next)
    };
@*/