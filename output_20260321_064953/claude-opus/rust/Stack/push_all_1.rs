use std::alloc::{dealloc, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@
pred Nodes(n: *mut Node; nodes: list<i32>) =
    if n == 0 {
        nodes == nil
    } else {
        (*n).value |-> ?v &*& (*n).next |-> ?next &*& struct_Node_padding(n) &*& alloc_block(n, std::mem::size_of::<Node>()) &*&
        Nodes(next, ?rest) &*& nodes == cons(v, rest)
    };

pred Stack(s: *mut Stack; nodes: list<i32>) =
    (*s).head |-> ?head &*& struct_Stack_padding(s) &*& alloc_block(s, std::mem::size_of::<Stack>()) &*&
    Nodes(head, nodes);

lem Nodes_append(n1: *mut Node)
    req Nodes(n1, ?vs1) &*& n1 != 0 &*& Nodes(?n2, ?vs2);
    ens Nodes(n1, append(vs1, vs2));
{
    open Nodes(n1, vs1);
    if (*n1).next == 0 {
        open Nodes(0, _);
        close Nodes(n2, vs2);
        (*n1).next = n2;
        close Nodes(n1, append(vs1, vs2));
    } else {
        Nodes_append((*n1).next);
        close Nodes(n1, append(vs1, vs2));
    }
}

lem Nodes_last_next(n: *mut Node)
    req Nodes(n, ?vs) &*& n != 0;
    ens Nodes(n, vs) &*& exists::<*mut Node>(?last) &*& last != 0;
{
    open Nodes(n, vs);
    if (*n).next == 0 {
        close Nodes(n, vs);
    } else {
        Nodes_last_next((*n).next);
        close Nodes(n, vs);
    }
}
@*/

impl Stack {
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
    //@ req Stack(stack, ?vs1) &*& Stack(other, ?vs2);
    //@ ens Stack(stack, append(vs2, vs1));
    {
        //@ open Stack(other, vs2);
        //@ open Stack(stack, vs1);
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        if !n.is_null() {
            //@ Nodes_last_next(head0);
            //@ open Nodes(head0, vs2);
            //@ close Nodes(head0, vs2);
            loop {
                //@ inv Nodes(head0, vs2) &*& (*stack).head |-> ?sh &*& struct_Stack_padding(stack) &*& alloc_block(stack, std::mem::size_of::<Stack>()) &*& Nodes(sh, vs1) &*& n != 0 &*& Nodes(n, ?vsn);
                //@ open Nodes(n, vsn);
                if (*n).next.is_null() {
                    //@ open Nodes(0 as *mut Node, _);
                    break;
                }
                n = (*n).next;
                //@ close Nodes(n, _);
            }

            (*n).next = (*stack).head;
            //@ close Nodes(n, _);
            //@ Nodes_append(head0);
            (*stack).head = head0;
        } else {
            //@ open Nodes(0 as *mut Node, vs2);
        }
        //@ close Stack(stack, append(vs2, vs1));
    }
}