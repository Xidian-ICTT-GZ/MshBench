use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ pred nodes_(n: *mut Node) = if n == 0 { true } else { (*n).next |-> ?next &*& (*n).value |-> ?v &*& std::alloc::alloc_block(n as *mut u8, std::alloc::Layout) &*& nodes_(next) };
//@ pred stack_(s: *mut Stack) = (*s).head |-> ?h &*& std::alloc::alloc_block(s as *mut u8, std::alloc::Layout) &*& nodes_(h);

type I32Predicate = unsafe fn(i32) -> bool;

unsafe fn filter_nodes(n: *mut Node, p: I32Predicate) -> *mut Node
//@ req nodes_(n);
//@ ens nodes_(result);
{
    if n.is_null() {
        //@ open nodes_(n);
        std::ptr::null_mut()
    } else {
        //@ open nodes_(n);
        
        let keep = p((*n).value);
        let next;
        if keep {
            next = filter_nodes((*n).next, p);
            
            
            (*n).next = next;
            
            //@ close nodes_(n);
            n
        } else {
            next = (*n).next;
            //@ open std::alloc::alloc_block(n as *mut u8, std::alloc::Layout);
            dealloc(n as *mut u8, Layout::new::<Node>());
            let result = filter_nodes(next, p);
            result
        }
    }
}

unsafe fn dispose_nodes(n: *mut Node)
//@ req nodes_(n);
//@ ens true;
{
    
    if !n.is_null() {
        //@ open nodes_(n);
        dispose_nodes((*n).next);
        //@ open std::alloc::alloc_block(n as *mut u8, std::alloc::Layout);
        dealloc(n as *mut u8, Layout::new::<Node>());
    } else {
        //@ open nodes_(n);
    }
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack_(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        
        //@ close nodes_(std::ptr::null_mut());
        //@ close stack_(stack);
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack_(stack);
//@ ens stack_(stack);
    {
        
        //@ open stack_(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        
        //@ close nodes_(n);
        //@ close stack_(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack_(stack) &*& (*stack).head |-> ?h &*& h != 0;
//@ ens stack_(stack);
    {
        
        //@ open stack_(stack);
        //@ open nodes_((*stack).head);
        let head = (*stack).head;
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ open std::alloc::alloc_block(head as *mut u8, std::alloc::Layout);
        dealloc(head as *mut u8, Layout::new::<Node>());
        
        //@ close stack_(stack);
        result
    }
    
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    //@ req stack_(stack);
//@ ens stack_(stack);
    {
        
        //@ open stack_(stack);
        let head = filter_nodes((*stack).head, p);
        
        (*stack).head = head;
        
        
        //@ close stack_(stack);
        
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req stack_(stack);
//@ ens true;
    {
        
        //@ open stack_(stack);
        dispose_nodes((*stack).head);
        //@ open std::alloc::alloc_block(stack as *mut u8, std::alloc::Layout);
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