use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens result != 0 &*& StackOwned(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close StackOwned(stack);
        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req StackOwned(stack);
    //@ ens StackOwned(stack);
    {
        //@ open StackOwned(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close StackOwned(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req StackOwned(stack);
    //@ ens StackOwned(stack);
    {
        //@ open StackOwned(stack);
        let head = (*stack).head;
        //@ open NodeOwned(head);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close StackOwned(stack);
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req StackOwned(stack);
    //@ ens true;
    {
        //@ open StackOwned(stack);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

//@ predicate StackOwned(*mut Stack stack) = struct_Stack_padding(stack) &*& (*stack).head |-> ?head &*& head == 0 ? true : NodeOwned(head);
//@ predicate NodeOwned(*mut Node node) = struct_Node_padding(node) &*& (*node).next |-> ?next &*& (*node).value |-> _ &*& next == 0 ? true : NodeOwned(next);

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