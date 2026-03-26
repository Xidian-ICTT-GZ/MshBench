use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred Nodes(n: *mut Node, count: i32) =
    if n == 0 {
        count == 0
    } else {
        (*n).next |-> ?next &*&
        (*n).value |-> ?v &*&
        Nodes(next, ?rest_count) &*&
        count == rest_count + 1
    };

pred Stack(s: *mut Stack, count: i32) =
    (*s).head |-> ?head &*&
    Nodes(head, count);

lem Nodes_append(n1: *mut Node)
    req Nodes(n1, ?c1) &*& n1 != 0 &*& Nodes(?n2, ?c2);
    ens Nodes(n1, c1 + c2);
{
    open Nodes(n1, c1);
    if (*n1).next == 0 {
        open Nodes((*n1).next, _);
    } else {
        Nodes_append((*n1).next);
    }
    close Nodes(n1, c1 + c2);
}

@*/

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens Stack(result, 0);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close Nodes(0, 0);
        //@ close Stack(stack, 0);
        stack
    }

    unsafe fn get_count(stack: *mut Stack) -> i32
    //@ req Stack(stack, ?count);
    //@ ens Stack(stack, count) &*& result == count;
    {
        //@ open Stack(stack, count);
        let head = (*stack).head;

        let mut n = head;
        let mut i = 0;
        //@ open Nodes(head, count);
        loop {
            //@ inv Nodes(n, ?remaining) &*& i == count - remaining;
            if n.is_null() {
                break;
            }
            //@ open Nodes(n, remaining);
            n = (*n).next;
            i += 1;
        }
        //@ close Nodes(head, count);
        //@ close Stack(stack, count);
        i
    }

    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
    //@ req Stack(stack, ?count1) &*& Stack(other, ?count2);
    //@ ens Stack(stack, count1 + count2);
    {
        //@ open Stack(other, count2);
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        if !n.is_null() {
            //@ open Nodes(head0, count2);
            loop {
                //@ inv Nodes(head0, count2) &*& n != 0;
                //@ open Nodes(n, ?remaining);
                if (*n).next.is_null() {
                    break;
                }
                n = (*n).next;
                //@ close Nodes(n, _);
            }
            //@ open Stack(stack, count1);
            (*n).next = (*stack).head;
            //@ close Nodes(n, count1 + 1);
            //@ Nodes_append(head0);
            (*stack).head = head0;
            //@ close Stack(stack, count1 + count2);
        } else {
            //@ open Nodes(head0, count2);
            //@ close Stack(stack, count1 + count2);
        }
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req Stack(stack, ?count);
    //@ ens Stack(stack, count + 1);
    {
        //@ open Stack(stack, count);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close Nodes(n, count + 1);
        //@ close Stack(stack, count + 1);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req Stack(stack, ?count) &*& count > 0;
    //@ ens Stack(stack, count - 1);
    {
        //@ open Stack(stack, count);
        let head = (*stack).head;
        //@ open Nodes(head, count);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close Stack(stack, count - 1);
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req Stack(stack, 0);
    //@ ens true;
    {
        //@ open Stack(stack, 0);
        //@ open Nodes((*stack).head, 0);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}