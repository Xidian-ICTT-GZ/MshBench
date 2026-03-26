use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}
struct Stack {
    head: *mut Node,
}

/*@

pred node(n: *mut Node, next: *mut Node, value: i32) =
    alloc_block_Node(n) &*& (*n).next |-> next &*& (*n).value |-> value;

pred nodes(h: *mut Node) =
    h == std::ptr::null_mut() ?
        true
    :
        node(h, ?nxt, ?v) &*& nodes(nxt);

pred stack(s: *mut Stack) =
    alloc_block_Stack(s) &*& (*s).head |-> ?h &*& nodes(h);

@*/

impl Stack {
    //@ req true;
    //@ ens stack(result);
    unsafe fn create() -> *mut Stack
    {
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
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        //@ open stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close node(n, (*stack).head, value);
        (*stack).head = n;
        //@ close stack(stack);
    }

    //@ req stack(stack);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack)
    {
        //@ open stack(stack);
        //@ open nodes(?h);
        //@ assert true;
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}