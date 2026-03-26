use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

predicate node_list(*mut Node ptr; ) =
    if ptr.is_null() {
        true
    } else {
        (*ptr).value |-> _ &*& (*ptr).next |-> ?next &*& node_list(next)
    };

predicate nodes_owned(*mut Node ptr; ) =
    if ptr.is_null() {
        true
    } else {
        (*ptr).value |-> _ &*& (*ptr).next |-> ?next &*& nodes_owned(next)
    };

lemma void dealloc_lemma(*mut Node node; )
    requires nodes_owned(node);
    ensures true;
{
    if !node.is_null() {
        open nodes_owned(node);
        let next = (*node).next;
        dealloc(node as *mut u8, Layout::new::<Node>());
        dealloc_lemma(next);
    }
}

#[requires(n != null_mut() &*& *n |-> ?head &*& node_list(head))]
#[ensures(*n |-> ?new_head &*& node_list(new_head))]
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate) {
    if !(*n).is_null() {
        let node = *n;
        open node_list(node);
        let val = (*node).value;
        let next = (*node).next;
        if p(val) {
            close node_list(next);
            let next_ptr = &mut (*node).next;
            filter_nodes(next_ptr, p);
            open node_list(*next_ptr);
            close node_list(node);
            *n = node;
        } else {
            close nodes_owned(node);
            dealloc_lemma(node);
            *n = next;
            filter_nodes(n, p);
        }
    }
}