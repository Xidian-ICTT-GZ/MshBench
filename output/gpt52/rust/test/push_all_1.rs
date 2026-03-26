use std::alloc::{dealloc, Layout};

struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@

predicate node_list(node: *mut Node, last: *mut Node) =
    node == last ?
        emp
    :
        (*node).next |-> ?nxt &*& node_list(nxt, last);

predicate stack(stack: *mut Stack, head: *mut Node, tail: *mut Node) =
    (*stack).head |-> head &*& node_list(head, tail);

@*/

impl Stack {
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
    //@ requires stack(stack, ?h1, ?t1) &*& stack(other, ?h0, ?t0) &*& other != stack;
    //@ ensures stack(stack, h0, t1) &*& node_list(t0, t1);
    {
        let head0 = (*other).head;
        //@ open stack(other, h0, t0);
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        if !n.is_null() {
            //@ assert node_list(head0, t0);
            loop {
                //@ invariant node_list(head0, t0) &*& node_list(head0, n) &*& n != t0;
                if (*n).next.is_null() {
                    break;
                }
                //@ open node_list(n, t0);
                n = (*n).next;
            }

            //@ open node_list(n, t0);
            //@ assert (*n).next |-> t0;
            //@ open stack(stack, h1, t1);
            (*n).next = (*stack).head;

            (*stack).head = head0;
            //@ close node_list(head0, t1);
            //@ close stack(stack, head0, t1);
        } else {
            //@ open stack(stack, h1, t1);
            //@ close stack(stack, h1, t1);
            //@ assert node_list(t0, t1);
        }
    }
}