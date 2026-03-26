//@ pred Node(node: *mut Node; value: i32, next: *mut Node) = 
//@   node != null_mut() &*& 
//@   struct_Node_padding(node) &*& 
//@   (*node).value |-> value &*& 
//@   (*node).next |-> next;

//@ pred Nodes(n: *mut *mut Node; nodes: list<*mut Node>) =
//@   n != null_mut() &*&
//@   *n |-> ?head &*&
//@   match nodes {
//@     nil => head == null_mut(),
//@     cons(h, t) => Node(h, ?v, ?next) &*& Nodes(&(*h).next, t)
//@   };

use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
//@ req n != null_mut() &*& *n |-> ?head &*& Nodes(n, ?nodes);
//@ ens n != null_mut() &*& *n |-> ?new_head &*& Nodes(n, ?filtered_nodes);
{
    if !(*n).is_null() {
        let node = *n;
        
        //@ open Nodes(n, _);
        //@ open Node(node, _, _);
        let keep = p((*node).value);
        if keep {
            let next_ptr = &mut (*node).next;
            //@ close Node(node, (*node).value, (*node).next);
            //@ assert next_ptr == &(*node).next;
            //@ assert Nodes(next_ptr, _);
            filter_nodes(next_ptr, p);
            //@ open Nodes(next_ptr, _);
            //@ close Nodes(n, cons(node, _));
            
        } else {
            let next_ = (*node).next;
            dealloc(node as *mut u8, Layout::new::<Node>());
            *n = next_;
            //@ assert Nodes(n, _);
            filter_nodes(n, p);
            //@ open Nodes(n, _);
            //@ close Nodes(n, _);
        }
    } else {
        //@ open Nodes(n, _);
        //@ close Nodes(n, nil);
    }
}