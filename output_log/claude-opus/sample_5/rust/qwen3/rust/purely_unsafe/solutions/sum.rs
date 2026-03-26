use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@
pred Nodes(n: *mut Node; sum: i32) =
    if n == 0 {
        sum == 0
    } else {
        (*n).next |-> ?next &*& (*n).value |-> ?value &*&
        Nodes(next, ?rest_sum) &*&
        sum == value + rest_sum
    };

pred StackInv(s: *mut Stack;) =
    (*s).head |-> ?head &*& Nodes(head, _);
@*/

/*@
lem void Nodes_sum_nonneg(n: *mut Node)
    req Nodes(n, ?sum);
    ens Nodes(n, sum);
{
    open Nodes(n, sum);
    if n != 0 {
        Nodes_sum_nonneg((*n).next);
    }
    close Nodes(n, sum);
}
@*/

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens StackInv(result);
    {
        let layout = Layout::new::<Stack>();
        let stack = alloc(layout) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(layout);
        }
        (*stack).head = std::ptr::null_mut();
        //@ close Nodes(0 as *mut Node, 0);
        //@ close StackInv(stack);
        stack
    }

    unsafe fn is_empty(stack: *mut Stack) -> bool
    //@ req StackInv(stack);
    //@ ens StackInv(stack);
    {
        //@ open StackInv(stack);
        let result = (*stack).head.is_null();
        //@ close StackInv(stack);
        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req StackInv(stack);
    //@ ens StackInv(stack);
    {
        //@ open StackInv(stack);
        let layout = Layout::new::<Node>();
        let n = alloc(layout) as *mut Node;
        if n.is_null() {
            handle_alloc_error(layout);
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close Nodes(n, value + _);
        //@ close StackInv(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req StackInv(stack) &*& (*stack).head |-> ?h &*& h != 0 &*& (*h).value |-> ?v &*& (*h).next |-> ?nxt &*& Nodes(nxt, _);
    //@ ens StackInv(stack) &*& result == v;
    {
        //@ open StackInv(stack);
        let head = (*stack).head;
        //@ open Nodes(head, _);
        let result = (*head).value;
        (*stack).head = (*head).next;
        let layout = Layout::new::<Node>();
        dealloc(head as *mut u8, layout);
        //@ close StackInv(stack);
        result
    }

    unsafe fn pop2(stack: *mut Stack) -> i32
    //@ req StackInv(stack);
    //@ ens StackInv(stack);
    {
        //@ open StackInv(stack);
        let head = (*stack).head;
        if head.is_null() {
            //@ close StackInv(stack);
            return 0;
        }
        //@ open Nodes(head, _);
        let result = (*head).value;
        (*stack).head = (*head).next;
        let layout = Layout::new::<Node>();
        dealloc(head as *mut u8, layout);
        //@ close StackInv(stack);
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req StackInv(stack);
    //@ ens true;
    {
        //@ open StackInv(stack);
        let mut n = (*stack).head;
        loop
        //@ inv Nodes(n, _);
        {
            //@ open Nodes(n, _);
            if n.is_null() {
                break;
            }
            let next = (*n).next;
            let layout = Layout::new::<Node>();
            dealloc(n as *mut u8, layout);
            n = next;
        }
        let layout = Layout::new::<Stack>();
        dealloc(stack as *mut u8, layout);
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
        Stack::pop2(s);
        Stack::pop2(s);
        Stack::dispose(s);
    }
}