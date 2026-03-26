use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

/*@
pred Nodes(n: *mut Node; nodes: list<i32>) =
    if n == 0 {
        nodes == nil
    } else {
        alloc_block_Node(n) &*&
        (*n).value |-> ?v &*&
        (*n).next |-> ?next &*&
        Nodes(next, ?rest) &*&
        nodes == cons(v, rest)
    };
@*/

//@ req *n |-> ?node &*& Nodes(node, ?nodes) &*& is_I32Predicate(p, ?pinfo);
//@ ens *n |-> ?node2 &*& Nodes(node2, ?nodes2) &*& is_I32Predicate(p, pinfo);
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
{
    //@ open Nodes(node, nodes);
    if !(*n).is_null() {
        let node = *n;
        
        let keep = p((*node).value);
        if keep {
            let next_ptr = &mut (*node).next;
            filter_nodes(next_ptr, p);
            //@ close Nodes(node, _);
        } else {
            let next_ = (*node).next;
            dealloc(node as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
        }
    } else {
        //@ close Nodes(0 as *mut Node, nil);
    }
}