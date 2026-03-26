//@ pred Nodes(*mut Node; list<i32>) = 
//@   match *0 {
//@     null => *1 == [],
//@     ?n => (*n).next |-> ?next &*& (*n).value |-> ?v &*& Nodes(next, ?vs) &*& *1 == cons(v, vs)
//@   };

//@ pred StackP(*mut Stack; list<i32>) = 
//@   (*0).head |-> ?h &*& Nodes(h, *1);

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
    
    
    {
        //@ open Nodes(?h, _);
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close StackP(stack, []);
        
        
        stack
    }

    unsafe fn get_count(stack: *mut Stack) -> i32
    
    
    {
        //@ open StackP(stack, ?vs);
        //@ assert Nodes(?h, vs);
        let head = (*stack).head;
        
        let mut n = head;
        let mut i = 0;
        
        loop {
            
            if n.is_null() {
                break;
            }
            //@ open Nodes(n, ?rest);
            n = (*n).next;
            i += 1;
            //@ close Nodes(n, rest);
            
        }
        //@ close StackP(stack, vs);
        
        
        
        i
    }

    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
    
    
    {
        //@ open StackP(other, ?other_vs);
        //@ open StackP(stack, ?stack_vs);
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;
        
        if !n.is_null() {
            //@ open Nodes(n, ?vs0);
            loop {
                

                if (*n).next.is_null() {
                    break;
                }
                //@ open Nodes((*n).next, ?vs1);
                n = (*n).next;
                //@ close Nodes(n, vs1);
                
                
            }
            //@ close Nodes(n, cons(?last, []));
            (*n).next = (*stack).head;
            //@ close Nodes(head0, append(other_vs, stack_vs));
            (*stack).head = head0;
        } else {
            //@ close Nodes(null, []);
        }
        //@ close StackP(stack, append(other_vs, stack_vs));
        
        
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    
    
    {
        //@ open StackP(stack, ?vs);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close Nodes(n, cons(value, vs));
        //@ close StackP(stack, cons(value, vs));
        
        
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    
    
    {
        //@ open StackP(stack, ?vs);
        //@ open Nodes(?h, ?vs0);
        let head = (*stack).head;
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close StackP(stack, tail(vs0));
        
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    
    
    {
        //@ open StackP(stack, _);
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