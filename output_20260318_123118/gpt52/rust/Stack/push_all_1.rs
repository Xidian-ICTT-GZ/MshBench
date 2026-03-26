use std::alloc::{dealloc, Layout};

struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@

predicate nodes(node: *mut Node, last: *mut Node) =
    node == last ?
        emp
    :
        node != 0 &*&
        (*node).next |-> ?nxt &*&
        nodes(nxt, last);

predicate stack(s: *mut Stack, last: *mut Node) =
    s != 0 &*&
    (*s).head |-> ?h &*&
    nodes(h, last);

@*/

impl Stack {
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
        //@ requires stack(stack, 0) &*& stack(other, 0);
        //@ ensures stack(stack, 0);
    {
        let head0 = (*other).head;
        //@ open stack(other, 0);
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        if !n.is_null() {
            //@ open nodes(head0, 0);
            loop
                //@ invariant n != 0 &*& nodes(head0, n) &*& (*n).next |-> ?nn &*& nodes(nn, 0) &*& stack(stack, 0);
            {
                if (*n).next.is_null() {
                    //@ assert (*n).next |-> 0;
                    //@ close nodes(0, 0);
                    break;
                }
                //@ open nodes(nn, 0);
                n = (*n).next;
            }

            //@ open stack(stack, 0);
            //@ open nodes((*stack).head, 0);
            (*n).next = (*stack).head;
            //@ close nodes((*stack).head, 0);
            //@ close nodes(head0, 0);

            (*stack).head = head0;
            //@ close stack(stack, 0);
        }
    }
}