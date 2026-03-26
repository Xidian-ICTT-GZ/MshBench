use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

/*@ pred node(p: *mut Node, v: i32, n: *mut Node) =
    p != null_mut::<Node>() &*&
    [1/2]p as *mut i32 |-> v &*&
    [1/2](p as *mut i32).offset(1) as *mut *mut Node |-> n;
@*/

/*@ pred nodes(p: *mut Node) =
    p == null_mut::<Node>() ? true :
    exists(?v, ?n) &*& node(p, v, n) &*& nodes(n);
@*/

type I32Predicate = fn(i32) -> bool;

//@ req *n |-> ?head &*& nodes(head) &*& full_borrow(?frac, predicate_nodes(n));
//@ ens *n |-> ?new_head &*& nodes(new_head);
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
{
    if !(*n).is_null() {
        let node = *n;
        //@ open nodes(node);
        //@ assert node(node, ?v, ?next);
        
        let keep = p((*node).value);
        if keep {
            let next_ptr = &mut (*node).next;
            //@ close node(node, v, next);
            //@ leak node(node, v, next);
            //@ full_borrow_into(predicate_nodes(next_ptr), frac);
            filter_nodes(next_ptr, p);
            //@ full_borrow_outof(predicate_nodes(next_ptr), frac);
            //@ open nodes(?filtered_next);
            //@ close nodes(filtered_next);
            //@ close node(node, v, filtered_next);
            //@ close nodes(node);
            
        } else {
            let next_ = (*node).next;
            //@ open node(node, v, next_);
            dealloc(node as *mut u8, Layout::new::<Node>());
            *n = next_;
            //@ full_borrow_into(predicate_nodes(n), frac);
            filter_nodes(n, p);
            //@ full_borrow_outof(predicate_nodes(n), frac);
        }
    } else {
        //@ close nodes(null_mut::<Node>());
    }
}