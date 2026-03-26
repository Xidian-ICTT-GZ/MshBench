use std::alloc::{Layout, dealloc};

struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@
predicate Node(n: *mut Node, next: *mut Node) = 
    struct_Node_padding(n) &*& (*n).next |-> next;

predicate Nodes(n: *mut Node; last: *mut Node) =
    if n.is_null() {
        last == n
    } else {
        Node(n, ?next) &*& Nodes(next, last)
    };

predicate Stack(s: *mut Stack, head: *mut Node) =
    struct_Stack_padding(s) &*& (*s).head |-> head &*& alloc_block(s as *mut u8, Layout::new_::<Stack>());

predicate StackNoAlloc(s: *mut Stack, head: *mut Node) =
    struct_Stack_padding(s) &*& (*s).head |-> head;

lemma fn nodes_last_not_null(n: *mut Node)
    requires Nodes(n, ?last) &*& n != std::ptr::null_mut();
    ensures Nodes(n, last) &*& last != std::ptr::null_mut();
{
    open Nodes(n, last);
    if (*n).next.is_null() {
        close Nodes(n, last);
    } else {
        nodes_last_not_null((*n).next);
        close Nodes(n, last);
    }
}

lemma fn nodes_append_lemma(n: *mut Node, m: *mut Node)
    requires Nodes(n, ?last) &*& last != std::ptr::null_mut() &*& Node(last, m) &*& Nodes(m, ?last2);
    ensures Nodes(n, last2);
{
    open Nodes(n, last);
    if n == last {
        close Nodes(m, last2);
        close Nodes(n, last2);
    } else {
        nodes_append_lemma((*n).next, m);
        close Nodes(n, last2);
    }
}

lemma fn nodes_split_last(n: *mut Node)
    requires Nodes(n, ?last) &*& n != std::ptr::null_mut();
    ensures Nodes(n, last) &*& last != std::ptr::null_mut();
{
    open Nodes(n, last);
    if (*n).next.is_null() {
        close Nodes(n, last);
    } else {
        nodes_split_last((*n).next);
        close Nodes(n, last);
    }
}
@*/

impl Stack {
    #[requires(StackNoAlloc(stack, ?h1) &*& Nodes(h1, ?last1) &*& Stack(other, ?h2) &*& Nodes(h2, ?last2))]
    #[ensures(StackNoAlloc(stack, ?h_new) &*& Nodes(h_new, ?last_new))]
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack) {
        //@ open Stack(other, h2);
        let head0 = (*other).head;
        //@ open StackNoAlloc(other, h2);
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        if !n.is_null() {
            //@ open Nodes(head0, last2);
            //@ close Nodes(head0, last2);
            //@ nodes_split_last(head0);
            
            #[invariant(StackNoAlloc(stack, h1) &*& Nodes(h1, last1) &*& 
                        Nodes(head0, ?curr_last) &*& curr_last != std::ptr::null_mut() &*&
                        n != std::ptr::null_mut() &*&
                        Node(n, ?n_next) &*& Nodes(n_next, curr_last))]
            loop {
                //@ open Nodes(n_next, curr_last);
                if (*n).next.is_null() {
                    //@ close Nodes(n_next, curr_last);
                    break;
                }
                //@ close Nodes(n_next, curr_last);
                //@ nodes_split_last(n_next);
                //@ close Nodes(head0, curr_last);
                //@ nodes_append_lemma(head0, n_next);
                n = (*n).next;
            }
            
            //@ open StackNoAlloc(stack, h1);
            (*n).next = (*stack).head;
            //@ close Node(n, h1);
            //@ close Nodes(h1, last1);
            //@ nodes_append_lemma(head0, h1);

            (*stack).head = head0;
            //@ close StackNoAlloc(stack, head0);
        } else {
            //@ open Nodes(head0, last2);
        }
    }
}