use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ pred node(n: *mut Node; next: *mut Node, value: i32) = n != 0 &*& struct_Node_padding(n) &*& (*n).next |-> next &*& (*n).value |-> value;
//@ pred stack(s: *mut Stack; head: *mut Node) = s != 0 &*& struct_Stack_padding(s) &*& (*s).head |-> head;

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack(result, 0);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close_struct(stack);
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack, 0);
        
        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(stack, ?old_head);
    //@ ens stack(stack, ?new_head) &*& node(new_head, old_head, value);
    {
        //@ open stack(stack, _);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ close_struct(n);
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close node(n, (*n).next, value);
        //@ close stack(stack, n);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack, ?head) &*& head != 0 &*& node(head, ?next, ?val);
    //@ ens stack(stack, next) &*& result == val;
    {
        //@ open stack(stack, _);
        let head = (*stack).head;
        //@ open node(head, _, _);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, (*stack).head);
        
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack, _);
    //@ ens true;
    {
        //@ open stack(stack, _);
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