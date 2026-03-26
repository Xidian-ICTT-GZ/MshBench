use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

/*@ pred node(node: *mut Node; value: i32, next: *mut Node) =
    alloc_block_(node as *u8, std::mem::size_of::<Node>()) &*&
    struct_Node_padding(node) &*&
    (*node).value |-> value &*&
    (*node).next |-> next;
@*/

/*@ pred nodes(n: *mut Node; vs: list<i32>) =
    n == null_mut::<Node>() ?
        vs == nil
    :
        exists(value: i32, rest: list<i32>).
            vs == cons(value, rest) &*&
            node(n, value, ?next) &*&
            nodes(next, rest);
@*/

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
//@ req *n |-> ?head &*& nodes(head, ?vs);
//@ ens *n |-> ?new_head &*& nodes(new_head, ?filtered_vs) &*& forall(vs, |v| p(v) || !mem(v, filtered_vs)) &*& forall(filtered_vs, |v| mem(v, vs) && p(v));
{
    if !(*n).is_null() {
        let node = *n;
        //@ open nodes(node, _);
        //@ assert node(node, ?val, ?next);

        let keep = p((*node).value);
        if keep {
            let next_ptr = &mut (*node).next;
            //@ close node(node, val, next);
            //@ assert *next_ptr |-> next;
            filter_nodes(next_ptr, p);
            //@ open node(node, val, ?new_next);
            //@ close nodes(node, cons(val, ?rest));
            
        } else {
            let next_ = (*node).next;
            //@ close node(node, val, next_);
            dealloc(node as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
        }
    }
}