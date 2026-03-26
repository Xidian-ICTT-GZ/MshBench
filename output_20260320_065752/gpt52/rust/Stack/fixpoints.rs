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

pred nodes(p: *mut Node) =
    p == std::ptr::null_mut() ?
        true
    :
        node(p, ?nxt, ?v) &*& nodes(nxt);

pred stack(s: *mut Stack) =
    std::alloc::alloc_block(s as *mut u8, Layout::new::<Stack>()) &*&
    (*s).head |-> ?h &*&
    nodes(h);

@*/

impl Stack {
    //@ req true;
    //@ ens stack(result);
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(std::ptr::null_mut());
        //@ close stack(stack);
        stack
    }

    //@ req stack(stack);
    //@ ens stack(stack);
    unsafe fn push(stack: *mut Stack, value: i32) {
        //@ open stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close node(n, (*stack).head, value);
        //@ close nodes(n);
        (*stack).head = n;
        //@ close stack(stack);
    }

    //@ req stack(stack) &*& nodes(?h) &*& h != std::ptr::null_mut();
    //@ ens stack(stack);
    unsafe fn pop(stack: *mut Stack) -> i32 {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes(head);
        //@ open node(head, ?nxt, ?v);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close nodes(nxt);
        //@ close stack(stack);
        result
    }

    //@ req stack(stack) &*& (*stack).head |-> std::ptr::null_mut();
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack) {
        //@ open stack(stack);
        //@ open nodes(std::ptr::null_mut());
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    unsafe {
        let s = Stack::create();
        //@ assert stack(s);
        Stack::push(s, 10);
        Stack::push(s, 20);
        //@ open stack(s);
        //@ assert nodes(?h1);
        //@ close stack(s);
        let result1 = Stack::pop(s);

        //@ open stack(s);
        //@ assert nodes(?h2);
        //@ close stack(s);
        let result2 = Stack::pop(s);

        //@ open stack(s);
        //@ assert (*s).head |-> std::ptr::null_mut();
        //@ close stack(s);
        Stack::dispose(s);
        let _ = result1;
        let _ = result2;
    }
}