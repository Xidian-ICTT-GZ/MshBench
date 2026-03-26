use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

//@ predicate nodes(*mut Node head) =
//@     head == std::ptr::null_mut() ?
//@         true :
//@         head |-> Node { next: ?next, value: _ } &*& nodes(next);

struct Stack {
    head: *mut Node,
}

//@ predicate stack(*mut Stack s, *mut Node head) =
//@     s |-> Stack { head: head } &*& nodes(head);

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ requires true;
    //@ ensures stack(result, std::ptr::null_mut());
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(std::ptr::null_mut());
        //@ close stack(stack, std::ptr::null_mut());
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ requires stack(stack, ?head);
    //@ ensures stack(stack, ?new_head) &*& new_head == _;
    {
        //@ open stack(stack, head);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = head;
        (*n).value = value;
        (*stack).head = n;
        //@ close nodes(head);
        //@ close nodes(n);
        //@ close stack(stack, n);
    }
    
    unsafe fn pop(stack: *mut Stack) -> i32
    //@ requires stack(stack, ?head) &*& head != std::ptr::null_mut();
    //@ ensures stack(stack, ?new_head) &*& result == _;
    {
        //@ open stack(stack, head);
        //@ open nodes(head);
        let head = (*stack).head;
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, (*head).next);
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ requires stack(stack, std::ptr::null_mut());
    //@ ensures true;
    {
        //@ open stack(stack, std::ptr::null_mut());
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