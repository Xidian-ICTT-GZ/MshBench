use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

//@ pred Nodes(*mut Node node; list<i32> vs) =
//@   match vs {
//@     Nil => node == null_mut(),
//@     Cons(v, vs1) => node != null_mut() && (*node).value |-> v &*& (*node).next |-> ?next &*& Nodes(next, vs1)
//@   };

type I32Predicate = fn(i32) -> bool;

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
//@ req *n |-> ?node &*& Nodes(node, ?vs);
//@ ens *n |-> ?node1 &*& Nodes(node1, ?vs1) &*& true;
{
    if !(*n).is_null() {
        let node = *n;
        
        //@ open Nodes(node, _);
        let keep = p((*node).value);
        if keep {
            let next_ptr = &mut (*node).next;
            //@ close Nodes((*node).next, _);
            filter_nodes(next_ptr, p);
            //@ open Nodes(_, _);
            //@ close Nodes(node, _);
            
        } else {
            let next_ = (*node).next;
            dealloc(node as *mut u8, Layout::new::<Node>());
            *n = next_;
            //@ close Nodes(next_, _);
            filter_nodes(n, p);
            //@ open Nodes(_, _);
        }
    }
    //@ if (*n).is_null() { close Nodes(null_mut(), nil); }
}