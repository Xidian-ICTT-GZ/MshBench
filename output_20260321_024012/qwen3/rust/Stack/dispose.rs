use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ pred nodes(n: *mut Node) = n == null ? true : 
//@   (exists(next: *mut Node, value: i32; 
//@     n |-> struct_Node { next: next, value: value } &*& nodes(next)));

//@ pred stack(s: *mut Stack) = s |-> struct_Stack { head: ?head } &*& nodes(head);

unsafe fn dispose_nodes(n: *mut Node)
//@ req nodes(n);
//@ ens true;
{
    
    if !n.is_null() {
        //@ open nodes(n);
        let next = (*n).next;
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(null);
        //@ close stack(stack);
        
        return stack;
    }
    
    unsafe fn is_empty(stack: *mut Stack) -> bool
    //@ req stack(stack);
    //@ ens stack(stack) &*& result == ((*stack).head == null);
    {
        
        let head = (*stack).head;
        
        let result = (*stack).head.is_null();
        //@ close stack(stack);
        
        return result;
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close nodes(n);
        //@ close stack(stack);
        
        
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack) &*& (*stack).head != null;
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes(head);
        let next = (*head).next;
        let result = (*head).value;
        (*stack).head = next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close nodes(next);
        //@ close stack(stack);
        
        return result;
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack);
    //@ ens true;
    {
        //@ open stack(stack);
        dispose_nodes((*stack).head);
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