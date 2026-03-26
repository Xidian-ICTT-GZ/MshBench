use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ pred nodes(n: *mut Node) = n == 0 ? true : (*n).next |-> ?next &*& (*n).value |-> ?v &*& nodes(next);
//@ pred stack(s: *mut Stack) = (*s).head |-> ?h &*& nodes(h);

type I32Predicate = unsafe fn(i32) -> bool;

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
//@ req *n |-> ?h &*& nodes(h);
//@ ens *n |-> ?h2 &*& nodes(h2);
{
    //@ open nodes(h);
    if !(*n).is_null() {
        //@ assert *n |-> ?hn &*& hn != 0;
        //@ open nodes(hn);
        //@ assert (*hn).next |-> ?next &*& (*hn).value |-> ?v &*& nodes(next);
        
        let keep = p((**n).value);
        if keep {
            //@ close nodes(next);
            filter_nodes(&raw mut (**n).next, p);
            //@ open (*hn).next |-> ?next2;
            //@ close nodes(hn);
            //@ close nodes(hn);
        } else {
            let next_ = (**n).next;
            //@ open nodes(next);
            dealloc(*n as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
        }
    } else {
        //@ close nodes(0);
    }
}

unsafe fn dispose_nodes(n: *mut Node)
//@ req nodes(n);
//@ ens true;
{
    //@ open nodes(n);
    if !n.is_null() {
        //@ open nodes((*n).next);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens result != 0 &*& stack(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(0);
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
        //@ open nodes(?h);
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close nodes((*stack).head);
        //@ close nodes(n);
        (*stack).head = n;
        //@ close stack(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack) &*& (*stack).head |-> ?h &*& h != 0;
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes(head);
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ close stack(stack);
        dealloc(head as *mut u8, Layout::new::<Node>());
        
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