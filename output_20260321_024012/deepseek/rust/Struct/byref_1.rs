use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

/*@
predicate nodes(n: *mut Node; count: int) =
    if n.is_null() {
        count == 0
    } else {
        alloc_block(n, std::mem::size_of::<Node>()) &*&
        struct_Node_padding(n) &*&
        (*n).value |-> ?v &*&
        (*n).next |-> ?next &*&
        nodes(next, ?next_count) &*&
        count == 1 + next_count
    };
@*/

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
    //@ req nodes(*n, ?count) &*& p is I32Predicate;
    //@ ens nodes(*n, ?new_count) &*& new_count <= count;
{
    if !(*n).is_null() {
        let node = *n;
        //@ open nodes(node, count);
        //@ assert nodes((*node).next, ?next_count);
        
        let keep = p((*node).value);
        if keep {
            let next_ptr = &mut (*node).next;
            filter_nodes(next_ptr, p);
            //@ close nodes(node, 1 + next_count);
        } else {
            let next_ = (*node).next;
            //@ open nodes(next_, ?next_count);
            //@ close nodes(next_, next_count);
            dealloc(node as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
        }
    } else {
        //@ open nodes(*n, count);
        //@ close nodes(*n, 0);
    }
}