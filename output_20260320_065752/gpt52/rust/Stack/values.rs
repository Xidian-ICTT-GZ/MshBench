use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred nodes(list: *mut Node) =
    list == std::ptr::null_mut() ?
        true
    :
        (*list).next |-> ?nxt &*& (*list).value |-> ?v &*& alloc_block_Node(list) &*& nodes(nxt);

pred stack(stack: *mut Stack) =
    (*stack).head |-> ?h &*& alloc_block_Stack(stack) &*& nodes(h);

@*/

impl Stack {
    //@ req true;
    //@ ens result == std::ptr::null_mut() ? true : stack(result);
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close nodes(std::ptr::null_mut());
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack);

        stack
    }

    //@ req stack(stack);
    //@ ens stack(stack);
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        //@ open stack(stack);
        //@ open nodes(?oldHead);

        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close nodes(oldHead);
        //@ close nodes(n);
        (*stack).head = n;

        //@ close stack(stack);
    }

    //@ req stack(stack);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack)
    {
        //@ open stack(stack);
        //@ open nodes(?h);
        //@ close nodes(h);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}