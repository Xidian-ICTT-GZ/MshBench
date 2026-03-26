use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

predicate nodes(struct Node* n) = 
    n != null_mut() &*& 
    n->value |-> ?v &*&
    n->next |-> ?next &*&
    nodes(next) || n == null_mut();

predicate nodes(struct Node* n, I32Predicate p) =
    n == null_mut() ? emp : 
    n->value |-> ?v &*& n->next |-> ?next &*&
    p(v) ?
        nodes(next, p) :
        nodes(next, p);

#[requires(n != null_mut() &*& *n |-> ?node &*& nodes(node, p))]
#[ensures(*n |-> ?node2 &*& nodes(node2, p))]
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
    
    
    
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