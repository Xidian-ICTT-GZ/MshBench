use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

/*@
pred struct_Node_padding(p: *mut Node;) = true; // Assuming padding does not own heap

pred alloc_block_Node(p: *mut Node;) = p |-> _;

pred Nodes(head: *mut Node;) =
    if head == 0 as *mut Node {
        emp
    } else {
        (*head).value |-> _ &*& (*head).next |-> ?next &*&
        struct_Node_padding(head) &*&
        alloc_block_Node(head) &*&
        Nodes(next)
    };

lem void Nodes_open_nonnull(head: *mut Node)
    requires Nodes(head) &*& head != 0 as *mut Node;
    ensures (*head).value |-> _ &*& (*head).next |-> ?next &*&
            struct_Node_padding(head) &*&
            alloc_block_Node(head) &*&
            Nodes(next);
{
    open Nodes(head);
}

lem void Nodes_close_null()
    requires emp;
    ensures Nodes(0 as *mut Node);
{
    close Nodes(0 as *mut Node);
}

lem void Nodes_close_nonnull(head: *mut Node)
    requires (*head).value |-> _ &*& (*head).next |-> ?next &*&
             struct_Node_padding(head) &*&
             alloc_block_Node(head) &*&
             Nodes(next) &*& head != 0 as *mut Node;
    ensures Nodes(head);
{
    close Nodes(head);
}
@*/

#[requires(n |-> ?head &*& Nodes(head))]
#[ensures(n |-> ?new_head &*& Nodes(new_head))]
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate) {
    //@ open Nodes(*n);
    if !(*n).is_null() {
        let node = *n;
        //@ assert (*node).value |-> ?v;
        //@ assert (*node).next |-> ?nxt;

        let keep = p((*node).value);
        if keep {
            //@ close Nodes(nxt);
            let next_ptr = &mut (*node).next;
            filter_nodes(next_ptr, p);
            //@ assert (*node).next |-> ?new_nxt;
            //@ assert Nodes(new_nxt);
            //@ close Nodes(node);
        } else {
            let next_ = (*node).next;
            dealloc(node as *mut u8, Layout::new::<Node>());
            *n = next_;
            //@ close Nodes(next_);
            filter_nodes(n, p);
        }
    } else {
        //@ close Nodes(0 as *mut Node);
    }
}