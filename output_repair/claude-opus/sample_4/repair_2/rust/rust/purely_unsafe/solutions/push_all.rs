use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred Nodes(n: *mut Node; count: i32) =
    if n == 0 as *mut Node {
        count == 0
    } else {
        (*n).next |-> ?next &*& (*n).value |-> ?value &*& Nodes(next, ?rest) &*& count == rest + 1
    };

pred Stack_inv(s: *mut Stack; count: i32) =
    (*s).head |-> ?head &*& Nodes(head, count);

lem Nodes_append(n1: *mut Node)
    req Nodes(n1, ?c1) &*& n1 != 0 as *mut Node &*& Nodes(?n2, ?c2);
    ens Nodes(n1, c1 + c2);
{
    open Nodes(n1, c1);
    if (*n1).next == 0 as *mut Node {
        open Nodes((*n1).next, _);
        (*n1).next = n2;
        close Nodes(n1, c1 + c2);
    } else {
        Nodes_append((*n1).next);
        close Nodes(n1, c1 + c2);
    }
}

@*/

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens Stack_inv(result, 0);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close Nodes(0 as *mut Node, 0);
        //@ close Stack_inv(stack, 0);
        stack
    }

    unsafe fn get_count(stack: *mut Stack) -> i32
    //@ req Stack_inv(stack, ?count);
    //@ ens Stack_inv(stack, count) &*& result == count;
    {
        //@ open Stack_inv(stack, count);
        let head = (*stack).head;

        let mut n = head;
        let mut i = 0;

        loop {
            //@ inv Nodes(n, ?remaining) &*& i + remaining == count &*& i >= 0;
            //@ open Nodes(n, remaining);
            if n.is_null() {
                //@ close Nodes(n, remaining);
                break;
            }

            n = (*n).next;
            i += 1;
            //@ close Nodes(n, remaining);
        }
        //@ close Stack_inv(stack, count);
        i
    }

    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
    //@ req Stack_inv(stack, ?c1) &*& Stack_inv(other, ?c2);
    //@ ens Stack_inv(stack, c1 + c2);
    {
        //@ open Stack_inv(other, c2);
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        if !n.is_null() {
            loop {
                //@ inv Nodes(head0, c2) &*& n != 0 as *mut Node;
                //@ open Nodes(n, _);
                if (*n).next.is_null() {
                    //@ open Stack_inv(stack, c1);
                    (*n).next = (*stack).head;
                    (*stack).head = head0;
                    //@ close Nodes(0 as *mut Node, 0);
                    //@ close Nodes(n, _);
                    //@ Nodes_append(head0);
                    //@ close Stack_inv(stack, c1 + c2);
                    break;
                }
                //@ close Nodes(n, _);
                n = (*n).next;
            }
        } else {
            //@ open Nodes(head0, c2);
            //@ close Stack_inv(stack, c1 + c2);
        }
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req Stack_inv(stack, ?count);
    //@ ens Stack_inv(stack, count + 1);
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ open Stack_inv(stack, count);
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close Nodes(n, count + 1);
        //@ close Stack_inv(stack, count + 1);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req Stack_inv(stack, ?count) &*& count > 0;
    //@ ens Stack_inv(stack, count - 1);
    {
        //@ open Stack_inv(stack, count);
        let head = (*stack).head;
        //@ open Nodes(head, count);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close Stack_inv(stack, count - 1);
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req Stack_inv(stack, 0);
    //@ ens true;
    {
        //@ open Stack_inv(stack, 0);
        //@ open Nodes(_, 0);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}