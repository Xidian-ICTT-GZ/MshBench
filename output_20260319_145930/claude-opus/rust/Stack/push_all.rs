use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
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
        (*n).next |-> ?next &*&
        (*n).value |-> ?value &*&
        Nodes(next, ?count0) &*&
        count == count0 + 1
    };

pred Stack(s: *mut Stack; count: i32) =
    alloc_block_Stack(s) &*&
    (*s).head |-> ?head &*&
    Nodes(head, count);

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
        //@ close Nodes(0 as *mut Node, 0);
        //@ close Stack(stack, 0);
        stack
    }

    unsafe fn get_count(stack: *mut Stack) -> i32
    //@ req Stack(stack, ?count);
    //@ ens Stack(stack, count) &*& result == count;
    {
        //@ open Stack(stack, count);
        let head = (*stack).head;
        //@ assert Nodes(head, count);
        let mut n = head;
        let mut i = 0;
        //@ open Nodes(n, count);
        loop {
            //@ inv Nodes(n, ?remaining) &*& i + remaining == count;
            if n.is_null() {
                //@ close Nodes(n, remaining);
                break;
            }
            //@ assert alloc_block_Node(n) &*& (*n).next |-> ?next &*& (*n).value |-> ?value &*& Nodes(next, ?count0);
            n = (*n).next;
            i += 1;
            //@ open Nodes(n, count0);
        }
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
        //@ open Nodes(head0, count2);
        if !n.is_null() {
            //@ assert alloc_block_Node(n) &*& (*n).next |-> ?next0 &*& (*n).value |-> ?value0 &*& Nodes(next0, ?count0);
            loop {
                //@ inv alloc_block_Node(n) &*& (*n).next |-> ?next &*& (*n).value |-> ?value &*& Nodes(next, ?remaining);
                if (*n).next.is_null() {
                    break;
                }
                //@ open Nodes(next, remaining);
                n = (*n).next;
            }
            //@ open Stack(stack, count1);
            (*n).next = (*stack).head;
            //@ close Nodes((*n).next, count1);
            //@ close Nodes(n, count1 + 1);
            (*stack).head = head0;
            //@ close Stack(stack, count1 + count2);
        } else {
            //@ close Nodes(0 as *mut Node, 0);
            //@ assert count2 == 0;
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
        //@ open Nodes(_, 0);
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