use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ pred nodes(n: *mut Node) = if n == 0 { true } else { (*n).next |-> ?next &*& (*n).value |-> ?v &*& std::alloc::alloc_block(n as *mut u8, std::mem::size_of::<Node>()) &*& nodes(next) };
//@ pred stack(s: *mut Stack) = (*s).head |-> ?h &*& std::alloc::alloc_block(s as *mut u8, std::mem::size_of::<Stack>()) &*& nodes(h);

type I32Predicate = unsafe fn(i32) -> bool;

unsafe fn filter_nodes(n: *mut Node, p: I32Predicate) -> *mut Node
//@ req nodes(n);
//@ ens nodes(result);
{
    if n.is_null() {
        //@ open nodes(n);
        std::ptr::null_mut()
    } else {
        //@ open nodes(n);
        
        let keep = p((*n).value);
        let next;
        if keep {
            next = filter_nodes((*n).next, p);
            
            
            (*n).next = next;
            
            //@ close nodes(n);
            n
        } else {
            next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            let result = filter_nodes(next, p);
            result
        }
    }
}

unsafe fn dispose_nodes(n: *mut Node)
//@ req nodes(n);
//@ ens true;
{
    
    if !n.is_null() {
        //@ open nodes(n);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    } else {
        //@ open nodes(n);
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
        
        
        //@ close nodes(std::ptr::null_mut());
        //@ close stack(stack);
        stack
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
    //@ req stack(stack) &*& (*stack).head |-> ?h &*& h != 0;
    //@ ens stack(stack);
    {
        
        //@ open stack(stack);
        //@ open nodes((*stack).head);
        let head = (*stack).head;
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        
        //@ close stack(stack);
        result
    }
    
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        
        //@ open stack(stack);
        let head = filter_nodes((*stack).head, p);
        
        (*stack).head = head;
        
        
        
        //@ close stack(stack);
        
        
        
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

unsafe fn neq_20(x: i32) -> bool
//@ req true;
//@ ens true;

{
    x != 20
}

fn main()

{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        

        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}