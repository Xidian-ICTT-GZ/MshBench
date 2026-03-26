//@ pred Nodes(*mut Node; list<i32>) = 
//@   match *0 {
//@     null => *1 == nil,
//@     ?n => (*n).next |-> ?next &*& (*n).value |-> ?v &*& Nodes(next, ?vs) &*& *1 == cons(v, vs)
//@   };
//@ pred StackPred(*mut Stack; list<i32>) = 
//@   (*0).head |-> ?h &*& Nodes(h, *1);

use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Predicate = unsafe fn(i32) -> bool;

unsafe fn filter_nodes(n: *mut Node, p: I32Predicate) -> *mut Node
//@ req Nodes(n, ?vs);
//@ ens Nodes(result, ?ws) &*& foreach(vs, (|v| p(v) || true)) == true;
{
    if n.is_null() {
        //@ close Nodes(std::ptr::null_mut(), nil);
        std::ptr::null_mut()
    } else {
        //@ open Nodes(n, _);
        let keep = p((*n).value);
        let next;
        if keep {
            next = filter_nodes((*n).next, p);
            //@ close Nodes(n, cons((*n).value, _));
            
            (*n).next = next;
            
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
//@ req Nodes(n, _);
//@ ens true;
{
    
    if !n.is_null() {
        //@ open Nodes(n, _);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens StackPred(result, nil);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close Nodes(std::ptr::null_mut(), nil);
        //@ close StackPred(stack, nil);
        
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req StackPred(stack, ?vs);
    //@ ens StackPred(stack, cons(value, vs));
    {
        //@ open StackPred(stack, vs);
        //@ open Nodes(?h, vs);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close Nodes(n, cons(value, vs));
        //@ close StackPred(stack, cons(value, vs));
        
        
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req StackPred(stack, cons(?v, ?vs));
    //@ ens StackPred(stack, vs) &*& result == v;
    {
        //@ open StackPred(stack, cons(v, vs));
        //@ open Nodes(?h, cons(v, vs));
        let head = (*stack).head;
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close StackPred(stack, vs);
        
        result
    }
    
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    //@ req StackPred(stack, ?vs);
    //@ ens StackPred(stack, ?ws) &*& foreach(vs, (|x| p(x) || true)) == true;
    {
        //@ open StackPred(stack, vs);
        let head = filter_nodes((*stack).head, p);
        //@ close StackPred(stack, _);
        (*stack).head = head;
        
        
        
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req StackPred(stack, _);
    //@ ens true;
    {
        //@ open StackPred(stack, _);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

unsafe fn neq_20(x: i32) -> bool
//@ req true;
//@ ens result == (x != 20);
{
    x != 20
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        

        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}