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
            alloc_block(node, Layout::new::<Node>()) &
            (*node).value |-> v &
            (*node).next |-> ?next &
            Nodes(next, vs)
    };

predicate I32Predicate(fn(i32) -> bool p;);

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
    #[requires(
        exists(list<i32> vs. 
            n |-> ?head &*& 
            Nodes(head, vs) &*&
            I32Predicate(p)
        )
    )]
    #[ensures(
        exists(list<i32> vs_filtered.
            n |-> ?new_head &*&
            Nodes(new_head, vs_filtered) &*&
            I32Predicate(p) &*&
            vs_filtered == filter(vs, p)
        )
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

lemma void filter(list<i32> xs, fn(i32) -> bool p)
    requires true;
    ensures true;
{
    
}