use std::alloc::{Layout, dealloc};

struct Node {
    value: i32,
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
        alloc_block_Node(n) &*&
        (*n).value |-> ?v &*&
        (*n).next |-> ?next &*&
        Nodes(next, ?c) &*&
        count == c + 1
    };

pred Stack(s: *mut Stack; count: i32) =
    alloc_block_Stack(s) &*&
    (*s).head |-> ?head &*&
    Nodes(head, count);
@*/

impl Stack {
    //@ req Stack(stack, ?c1) &*& Stack(other, ?c2);
    //@ ens Stack(stack, c1 + c2);
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
    {
        //@ open Stack(other, c2);
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        if !n.is_null() {
            //@ open Nodes(head0, c2);
            //@ close Nodes(head0, c2);
            loop {
                //@ inv Nodes(head0, c2) &*& c2 > 0 &*& n != 0 &*& Nodes(n, ?cn) &*& cn > 0;
                //@ open Nodes(n, cn);
                if (*n).next.is_null() {
                    //@ close Nodes(0, 0);
                    break;
                }
                n = (*n).next;
                //@ close Nodes(n, cn - 1);
            }

            //@ open Stack(stack, c1);
            (*n).next = (*stack).head;
            //@ close Nodes(n, c1 + 1);
            (*stack).head = head0;
            //@ close Stack(stack, c1 + c2);
        } else {
            //@ open Nodes(head0, c2);
            //@ open Stack(stack, c1);
            //@ close Stack(stack, c1);
        }
    }
}