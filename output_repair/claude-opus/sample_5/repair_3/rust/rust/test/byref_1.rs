use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

/*@
pred Nodes(n: *mut Node; allNodes: list<i32>) =
    if n == 0 {
        allNodes == nil
    } else {
        (*n).value |-> ?v &*& (*n).next |-> ?next &*& struct_Node_padding(n) &*&
        Nodes(next, ?restNodes) &*& allNodes == cons(v, restNodes)
    };

pred Nodes_ptr(p: *mut *mut Node; n: *mut Node) =
    *p |-> n;
@*/

/*@
lem Nodes_null_inv()
    req Nodes(0, ?ns);
    ens Nodes(0, ns) &*& ns == nil;
{
    open Nodes(0, ns);
    close Nodes(0, nil);
}
@*/

/*@
lem Nodes_nonnull_inv(n: *mut Node)
    req Nodes(n, ?ns) &*& n != 0;
    ens (*n).value |-> ?v &*& (*n).next |-> ?next &*& struct_Node_padding(n) &*&
        Nodes(next, ?restNodes) &*& ns == cons(v, restNodes);
{
    open Nodes(n, ns);
}
@*/

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
//@ req Nodes_ptr(n, ?head) &*& Nodes(head, ?vs);
//@ ens Nodes_ptr(n, ?newHead) &*& Nodes(newHead, ?newVs);
{
    //@ open Nodes_ptr(n, head);
    if !(*n).is_null() {
        let node = *n;
        //@ open Nodes(node, vs);

        let keep = p((*node).value);
        if keep {
            let next_ptr = &mut (*node).next;
            //@ close Nodes_ptr(next_ptr, (*node).next);
            filter_nodes(next_ptr, p);
            //@ open Nodes_ptr(next_ptr, ?newNext);
            //@ close Nodes(node, _);
            //@ close Nodes_ptr(n, node);
        } else {
            let next_ = (*node).next;
            dealloc(node as *mut u8, Layout::new::<Node>());
            *n = next_;
            //@ close Nodes_ptr(n, next_);
            filter_nodes(n, p);
        }
    } else {
        //@ close Nodes_ptr(n, head);
    }
}