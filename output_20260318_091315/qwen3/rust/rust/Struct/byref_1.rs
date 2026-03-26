use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

predicate Nodes(*mut Node node; list<i32> values) =
    match values {
        [] => node == null_mut(),
        v :: vs => 
            alloc_block(node, Layout::new::<Node>()) &*&
            struct_Node_padding(node) &*&
            (*node).value |-> v &*&
            (*node).next |-> ?next &*&
            Nodes(next, vs)
    };

predicate I32Predicate(fn: I32Predicate) = true;

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
    #[requires(
        *n |-> ?head &*&
        Nodes(head, ?vs) &*&
        I32Predicate(p) &*&
        foreach(vs, |v| bool(v))
    )]
    #[ensures(
        *n |-> ?new_head &*&
        Nodes(new_head, ?filtered_vs) &*&
        foreach(filtered_vs, |v| p(v)) &*&
        foreach(vs, |v| p(v) || mem(v, filtered_vs) == false)
    )]
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