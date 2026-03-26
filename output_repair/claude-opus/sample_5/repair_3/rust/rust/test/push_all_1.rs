use std::alloc::{dealloc, Layout};

struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@

pred Nodes(n: *mut Node; count: i32) =
    if n == 0 {
        count == 0
    } else {
        count > 0 &*&
        (*n).next |-> ?next &*&
        Nodes(next, count - 1)
    };

pred Stack_own(s: *mut Stack; count: i32) =
    (*s).head |-> ?head &*&
    Nodes(head, count);

lem Nodes_append(n1: *mut Node)
    req Nodes(n1, ?c1) &*& c1 > 0 &*& Nodes(?n2, ?c2);
    ens Nodes(n1, c1 + c2);
{
    open Nodes(n1, c1);
    if (*n1).next == 0 {
        open Nodes((*n1).next, c1 - 1);
        (*n1).next = n2;
        close Nodes(n1, c1 + c2);
    } else {
        Nodes_append((*n1).next);
        close Nodes(n1, c1 + c2);
    }
}

@*/

impl Stack {
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
    //@ req Stack_own(stack, ?sc) &*& Stack_own(other, ?oc) &*& alloc_block(other as *mut u8, Layout::new_::<Stack>());
    //@ ens Stack_own(stack, sc + oc);
    {
        //@ open Stack_own(other, oc);
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        if !n.is_null() {
            //@ open Nodes(head0, oc);
            //@ close Nodes(head0, oc);
            loop
            //@ req Nodes(n, ?rem) &*& rem > 0 &*& n != 0;
            //@ ens Nodes(old_n, rem) &*& (*old_n).next |-> 0 &*& n == old_n;
            {
                //@ open Nodes(n, rem);
                if (*n).next.is_null() {
                    //@ open Nodes((*n).next, rem - 1);
                    //@ close Nodes(n, 1);
                    break;
                }
                //@ close Nodes(n, rem);
                //@ open Nodes(n, rem);
                let next = (*n).next;
                //@ close Nodes(n, rem);
                n = next;
            }

            //@ open Stack_own(stack, sc);
            //@ open Nodes(n, 1);
            (*n).next = (*stack).head;
            //@ close Nodes(n, sc + 1);
            //@ Nodes_append(head0);
            (*stack).head = head0;
            //@ close Stack_own(stack, sc + oc);
        } else {
            //@ open Nodes(head0, oc);
            //@ open Stack_own(stack, sc);
            //@ close Stack_own(stack, sc + oc);
        }
    }
}