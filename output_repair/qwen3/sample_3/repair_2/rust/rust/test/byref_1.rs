use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

predicate node_list(ptr: *mut Node) {
    if ptr.is_null() {
        true
    } else {
        (*ptr).value |-> _ && (*ptr).next |-> ?next && node_list(next)
    }
}

predicate nodes_owned(ptr: *mut Node) {
    if ptr.is_null() {
        true
    } else {
        (*ptr).value |-> _ && (*ptr).next |-> ?next && nodes_owned(next)
    }
}

lemma void dealloc_lemma(*mut Node node;)
    requires nodes_owned(node);
    ensures true;
{
    if !node.is_null() {
        let next = (*node).next;
        close nodes_owned(next);
        open nodes_owned(node);
        dealloc(node as *mut u8, Layout::new::<Node>());
    }
}

#[requires(n != null_mut() && *n |-> ?head && node_list(head))]
#[ensures(*n |-> ?new_head && node_list(new_head))]
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate) {
    if !(*n).is_null() {
        let node = *n;
        let val = (*node).value;
        let next_ptr = &(*node).next;
        let next_val = *next_ptr;
        open node_list(node);
        if p(val) {
            close node_list(next_val);
            let next_mut_ptr = &mut (*node).next;
            filter_nodes(next_mut_ptr, p);
            open node_list(*next_mut_ptr);
            close node_list(node);
        } else {
            close nodes_owned(node);
            dealloc_lemma(node);
            *n = next_val;
            filter_nodes(n, p);
        }
    }
}