use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

/*@
predicate struct_Node_padding(Node* n;) =
    0 == 0; // Dummy padding predicate placeholder

predicate Nodes(struct Node* head;) =
    head == 0 ? emp
    : head->value |-> _ &*& head->next |-> ?next &*&
      struct_Node_padding(head) &*&
      alloc_block<Node>(head) &*&
      Nodes(next);

lemma void Nodes_open_nonnull(struct Node* head)
    requires Nodes(head) &*& head != 0;
    ensures head->value |-> _ &*& head->next |-> ?next &*&
            struct_Node_padding(head) &*&
            alloc_block<Node>(head) &*&
            Nodes(next);
{
    open Nodes(head);
}

lemma void Nodes_close_null()
    requires emp;
    ensures Nodes(0);
{
    close Nodes(0);
}

lemma void Nodes_close_nonnull(struct Node* head)
    requires head->value |-> _ &*& head->next |-> ?next &*&
             struct_Node_padding(head) &*&
             alloc_block<Node>(head) &*&
             Nodes(next) &*& head != 0;
    ensures Nodes(head);
{
    close Nodes(head);
}
@*/

#[requires(*n |-> ?head &*& Nodes(head))]
#[ensures(*n |-> ?new_head &*& Nodes(new_head))]
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate) {
    //@ open Nodes(head);
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