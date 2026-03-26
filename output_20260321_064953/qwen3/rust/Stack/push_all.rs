use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ pred Nodes(node: *mut Node; values: list<i32>) =
//@   match values {
//@     nil => node == std::ptr::null_mut(),
//@     cons(v, vs) => node != std::ptr::null_mut() && (*node).value |-> v &*& (*node).next |-> ?next &*& Nodes(next, vs)
//@   };

//@ pred StackP(stack: *mut Stack; values: list<i32>) =
//@   stack != std::ptr::null_mut() &*&
//@   (*stack).head |-> ?head &*&
//@   Nodes(head, values);

impl Stack {

    unsafe fn create() -> *mut Stack
    
    
    {
        //@ req true;
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close Nodes(std::ptr::null_mut(), nil);
        //@ close StackP(stack, nil);
        
        
        stack
        //@ ens stack != std::ptr::null_mut() &*& StackP(stack, nil);
    }

    unsafe fn get_count(stack: *mut Stack) -> i32
    
    
    {
        //@ req StackP(stack, ?values);
        //@ open StackP(stack, values);
        //@ assert (*stack).head |-> ?head;
        let head = (*stack).head;
        
        let mut n = head;
        let mut i = 0;
        //@ let mut current_values = values;
        //@ while n != std::ptr::null_mut()
        //@   invariant Nodes(n, current_values) &*& i + length(current_values) == length(values);
        loop {
            
            if n.is_null() {
                break;
            }
            //@ open Nodes(n, current_values);
            //@ let v = head(current_values);
            //@ current_values = tail(current_values);
            n = (*n).next;
            i += 1;
            
        }
        //@ assert current_values == nil;
        //@ close StackP(stack, values);
        
        
        
        i
        //@ ens StackP(stack, values) &*& result == length(values);
    }

    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
    
    
    {
        //@ req StackP(stack, ?s_values) &*& StackP(other, ?o_values);
        //@ open StackP(other, o_values);
        //@ open StackP(stack, s_values);
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;
        
        if !n.is_null() {
            //@ open Nodes(n, o_values);
            //@ let mut current = tail(o_values);
            //@ while !(*n).next.is_null()
            //@   invariant Nodes((*n).next, current) &*& n != std::ptr::null_mut() &*& current != nil;
            loop {
                

                if (*n).next.is_null() {
                    break;
                }
                //@ open Nodes((*n).next, current);
                //@ current = tail(current);
                n = (*n).next;
                
                
            }
            //@ assert current == nil;
            //@ close Nodes((*n).next, s_values);
            (*n).next = (*stack).head;
            
            
            (*stack).head = head0;
            //@ close Nodes(head0, append(o_values, s_values));
        } else {
            //@ assert o_values == nil;
            //@ close Nodes(head0, s_values);
            (*stack).head = head0;
        }
        //@ close StackP(stack, append(o_values, s_values));
        
        
    }
    //@ ens StackP(stack, append(o_values, s_values));

    unsafe fn push(stack: *mut Stack, value: i32)
    
    
    {
        //@ req StackP(stack, ?values);
        //@ open StackP(stack, values);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close Nodes(n, cons(value, values));
        //@ close StackP(stack, cons(value, values));
        
        
    }
    //@ ens StackP(stack, cons(value, values));

    unsafe fn pop(stack: *mut Stack) -> i32
    
    
    {
        //@ req StackP(stack, ?values) &*& values != nil;
        //@ open StackP(stack, values);
        //@ open Nodes(?head, values);
        let head = (*stack).head;
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close StackP(stack, tail(values));
        
        result
        //@ ens StackP(stack, tail(values)) &*& result == head(values);
    }

    unsafe fn dispose(stack: *mut Stack)
    
    
    {
        //@ req StackP(stack, _);
        //@ open StackP(stack, _);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
    //@ ens true;

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