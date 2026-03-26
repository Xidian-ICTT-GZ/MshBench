use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ ghost predicate node_ptr(n: *mut Node) = n != null() ==> node_content(n);
//@ ghost predicate node_content(n: *mut Node) = ptr(n).next |-> ?next && ptr(n).value |-> ?value;
//@ ghost predicate stack_ptr(s: *mut Stack) = s != null() ==> stack_content(s);
//@ ghost predicate stack_content(s: *mut Stack) = ptr(s).head |-> ?h && (h == null() || node_ptr(h));

unsafe fn dispose_nodes(n: *mut Node)
{
    
    if !n.is_null() {
        //@ open node_content(n);
        let next_node = (*n).next;
        dispose_nodes(next_node);
        close node_content(n);
        dealloc(n as *mut u8, Layout::new::<Node>());
        
    }
}

impl Stack {

    unsafe fn create() -> *mut Stack
    
    
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        
        
        return stack;
    }
    
    unsafe fn is_empty(stack: *mut Stack) -> bool
    
    
    {
        
        let _head = (*stack).head;
        
        let result = (*stack).head.is_null();
        
        
        return result;
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    
    
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
    
    
    {
        
        let head = (*stack).head;
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        
        return result;
    }
    
    unsafe fn dispose(stack: *mut Stack)
    
    
    {
        
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

fn main()

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