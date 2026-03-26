use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

/*@ pred node(struct Node *n;) =
    n != 0 &*&
    malloc_block_Node(n) &*&
    n->value |-> _ &*&
    n->next |-> _;
@*/

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

//@ req true;
//@ ens true;
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
{
    if !(*n).is_null() {
        let node = *n;
        
        let keep = p((*node).value);
        if keep {
            let next_ptr = &mut (*node).next;
            filter_nodes(next_ptr, p);
            
        } else {
            //@ open node(node);
            let next_ = (*node).next;
            dealloc(node as *mut u8, Layout::new::<Node>());
            *n = next_;
            //@ close node(next_);
            filter_nodes(n, p);
        }
    }
}