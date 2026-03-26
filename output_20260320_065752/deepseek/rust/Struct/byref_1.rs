use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

/*@
pred node(n: *mut Node; value: i32, next: *mut Node) =
    alloc_block(n, std::mem::size_of::<Node>()) &*&
    struct_Node_padding(n) &*&
    (*n).value |-> value &*&
    (*n).next |-> next;
@*/

type I32Predicate = fn(i32) -> bool;

//@ req list(n, _) &*& is_i32predicate(p);
//@ ens list(n, _);
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
{
    if !(*n).is_null() {
        let node = *n;
        //@ open list(node, _);
        //@ open node(node, _, _);
        
        let keep = p((*node).value);
        if keep {
            let next_ptr = &mut (*node).next;
            //@ close node(node, (*node).value, (*node).next);
            //@ close list(node, _);
            filter_nodes(next_ptr, p);
            //@ close list(node, _);
        } else {
            let next_ = (*node).next;
            //@ close node(node, _, _);
            dealloc(node as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
        }
    } else {
        //@ close list(null_mut(), _);
    }
}

/*@
pred list(n: *mut Node; values: list<i32>) =
    n == null_mut() ?
        values == nil
    :
        node(n, ?v, ?next) &*&
        list(next, ?vs) &*&
        values == cons(v, vs);
@*/