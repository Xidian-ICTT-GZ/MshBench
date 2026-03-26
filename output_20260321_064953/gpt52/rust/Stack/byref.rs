use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ pred nodes_list(n: *mut Node) =
//@     n == std::ptr::null_mut() ? true :
//@     (*n).next |-> ?next &*& (*n).value |-> ?v &*& std::alloc::alloc_block(n as *mut u8, Layout::new::<Node>()) &*& nodes_list(next);

//@ pred stack(s: *mut Stack) =
//@     (*s).head |-> ?h &*& std::alloc::alloc_block(s as *mut u8, Layout::new::<Stack>()) &*& nodes_list(h);

type I32Predicate = unsafe fn(i32) -> bool;

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
//@ req n |-> ?head &*& nodes_list(head);
//@ ens n |-> ?head2 &*& nodes_list(head2);
{
    if !(*n).is_null() {
        //@ open nodes_list(*n);
        let keep = p((**n).value);
        if keep {
            filter_nodes(&raw mut (**n).next, p);
            //@ close nodes_list(*n);
        } else {
            let next_ = (**n).next;
            //@ open std::alloc::alloc_block(*n as *mut u8, Layout::new::<Node>());
            dealloc(*n as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
        }
    }
}

unsafe fn dispose_nodes(n: *mut Node)
//@ req nodes_list(n);
//@ ens true;
{
    
    if !n.is_null() {
        //@ open nodes_list(n);
        dispose_nodes((*n).next);
        //@ open std::alloc::alloc_block(n as *mut u8, Layout::new::<Node>());
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
        //@ close nodes_list(std::ptr::null_mut());
        //@ close stack(stack);
        
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        //@ open nodes_list((*stack).head);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close nodes_list(n);
        (*stack).head = n;
        //@ close stack(stack);
        
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack) &*& (*stack).head != std::ptr::null_mut();
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes_list(head);
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ open std::alloc::alloc_block(head as *mut u8, Layout::new::<Node>());
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack);
        
        result
    }
    
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        
        filter_nodes(&raw mut (*stack).head, p);
        
        //@ close stack(stack);
        
        
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack);
    //@ ens true;
    {
        //@ open stack(stack);
        
        dispose_nodes((*stack).head);
        //@ open std::alloc::alloc_block(stack as *mut u8, Layout::new::<Stack>());
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

unsafe fn neq_20(x: i32) -> bool
//@ req true;
//@ ens true;
{
    x != 20
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        

        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}