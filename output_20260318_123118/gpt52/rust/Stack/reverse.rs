use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred node(p: *mut Node, next: *mut Node, v: i32) =
    std::alloc::alloc_block(p as *mut u8, Layout::new::<Node>()) &*&
    (*p).next |-> next &*&
    (*p).value |-> v;

pred nodes(h: *mut Node) =
    if h == std::ptr::null_mut() {
        emp
    } else {
        (*h).next |-> ?nxt &*& (*h).value |-> ?v &*& std::alloc::alloc_block(h as *mut u8, Layout::new::<Node>()) &*& nodes(nxt)
    };

pred stack(s: *mut Stack, h: *mut Node) =
    std::alloc::alloc_block(s as *mut u8, Layout::new::<Stack>()) &*&
    (*s).head |-> h &*&
    nodes(h);

@*/

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ requires emp;
    //@ ensures stack(result, std::ptr::null_mut());
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ requires stack(stack, ?h);
    //@ ensures stack(stack, ?h2);
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ requires stack(stack, ?h) &*& h != std::ptr::null_mut();
    //@ ensures stack(stack, ?h2);
    {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    unsafe fn reverse(stack: *mut Stack)
    //@ requires stack(stack, ?h);
    //@ ensures stack(stack, ?h2);
    {
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();

        loop {
            //@ invariant (*stack).head |-> ?sh &*& std::alloc::alloc_block(stack as *mut u8, Layout::new::<Stack>()) &*& nodes(n) &*& nodes(m);
            if n.is_null() {
                break;
            }

            let next = (*n).next;

            (*n).next = m;
            m = n;
            n = next;
        }

        (*stack).head = m;
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ requires stack(stack, std::ptr::null_mut());
    //@ ensures emp;
    {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main()
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        let result1 = Stack::pop(s);

        let result2 = Stack::pop(s);

        Stack::dispose(s);
    }
}