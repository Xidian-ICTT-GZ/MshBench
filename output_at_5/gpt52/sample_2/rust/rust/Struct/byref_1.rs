use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

/*@

pred node_ptr(ptr: *mut Node; next: *mut Node) =
    ptr != 0 &*& struct_Node_value(ptr, _) &*& struct_Node_next(ptr, next);

pred nodes(list: *mut Node) =
    list == 0 ?
        true
    :
        node_ptr(list, ?nxt) &*& nodes(nxt);

@*/

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
    //@ req n != 0 &*& *n |-> ?head &*& nodes(head);
    //@ ens *n |-> ?head2 &*& nodes(head2);
{
    //@ open nodes(?head0);
    //@ close nodes(head0);
    if !(*n).is_null() {
        //@ assert *n |-> ?head1;
        //@ open nodes(head1);
        let node = *n;
        //@ assert node_ptr(node, ?old_next) &*& nodes(old_next);
        
        let keep = p((*node).value);
        if keep {
            let next_ptr = &mut (*node).next;
            //@ assert next_ptr == (node as *mut Node + 0) + 0; // dummy to help VF keep track (no effect if ignored)
            //@ open node_ptr(node, old_next);
            //@ close node_ptr(node, old_next);
            //@ close nodes(old_next);
            //@ close nodes(node);
            filter_nodes(next_ptr, p);
            //@ open nodes(node);
            //@ open node_ptr(node, ?new_next);
            //@ close node_ptr(node, new_next);
            //@ close nodes(new_next);
            //@ close nodes(node);
            
        } else {
            let next_ = (*node).next;
            //@ open node_ptr(node, old_next);
            dealloc(node as *mut u8, Layout::new::<Node>());
            *n = next_;
            //@ close nodes(old_next);
            filter_nodes(n, p);
        }
    } else {
        //@ assert *n |-> ?h;
        //@ open nodes(h);
        //@ close nodes(h);
    }
}