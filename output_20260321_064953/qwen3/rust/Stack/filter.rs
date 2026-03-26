//@ predicate Nodes(*mut Node; list<i32>) = 
//@   match *0 {
//@     null => *1 == nil,
//@     ?n => *1 == cons(?v, ?vs) &*& 
//@           struct_Node_padding(n) &*&
//@           (*n).value |-> v &*&
//@           (*n).next |-> ?next &*&
//@           Nodes(next, vs)
//@   };

//@ predicate StackP(*mut Stack; list<i32>) =
//@   struct_Stack_padding(*0) &*&
//@   (*0).head |-> ?h &*&
//@   Nodes(h, *1);

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
//@ ens Nodes(result, ?ws) &*& foreach(vs, (fun(x: i32) => p(x) || mem(x, ws))) == true &*& foreach(ws, (fun(x: i32) => mem(x, vs) && p(x))) == true;
{
    if n.is_null() {
        //@ close Nodes(std::ptr::null_mut(), nil);
        std::ptr::null_mut()
    } else {
        //@ open Nodes(n, vs);
        //@ assert struct_Node_padding(n);
        //@ assert (*n).value |-> ?v;
        //@ assert (*n).next |-> ?next_n;
        //@ assert Nodes(next_n, ?tail_vs);
        let keep = p((*n).value);
        let next;
        if keep {
            //@ close Nodes(next_n, tail_vs);
            next = filter_nodes((*n).next, p);
            //@ open Nodes(next, ?filtered_tail);
            //@ close Nodes(n, cons(v, filtered_tail));
            
            (*n).next = next;
            
            n
        } else {
            next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            //@ close Nodes(next, tail_vs);
            let result = filter_nodes(next, p);
            //@ open Nodes(result, ?filtered_tail);
            //@ close Nodes(result, filtered_tail);
            result
        }
    }
}

unsafe fn dispose_nodes(n: *mut Node)
//@ req Nodes(n, _);
//@ ens true;
{
    
    if !n.is_null() {
        //@ open Nodes(n, ?vs);
        //@ assert struct_Node_padding(n);
        //@ assert (*n).next |-> ?next_n;
        //@ close Nodes(next_n, ?tail_vs);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens StackP(result, nil);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close Nodes(std::ptr::null_mut(), nil);
        //@ close StackP(stack, nil);
        
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req StackP(stack, ?old_vals);
    //@ ens StackP(stack, cons(value, old_vals));
    {
        //@ open StackP(stack, old_vals);
        //@ assert (*stack).head |-> ?old_head;
        //@ close Nodes(old_head, old_vals);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close Nodes(n, cons(value, old_vals));
        //@ close StackP(stack, cons(value, old_vals));
        
        
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req StackP(stack, cons(?hd, ?tl));
    //@ ens StackP(stack, tl) &*& result == hd;
    {
        //@ open StackP(stack, cons(hd, tl));
        //@ assert (*stack).head |-> ?head;
        //@ open Nodes(head, cons(hd, tl));
        //@ assert struct_Node_padding(head);
        //@ assert (*head).value |-> hd;
        //@ assert (*head).next |-> ?next_head;
        //@ close Nodes(next_head, tl);
        let head = (*stack).head;
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close StackP(stack, tl);
        
        result
    }
    
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    //@ req StackP(stack, ?vs);
    //@ ens StackP(stack, ?ws) &*& foreach(vs, (fun(x: i32) => p(x) || mem(x, ws))) == true &*& foreach(ws, (fun(x: i32) => mem(x, vs) && p(x))) == true;
    {
        //@ open StackP(stack, vs);
        //@ assert (*stack).head |-> ?h;
        //@ close Nodes(h, vs);
        let head = filter_nodes((*stack).head, p);
        //@ open Nodes(head, ?ws);
        (*stack).head = head;
        //@ close StackP(stack, ws);
        
        
        
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req StackP(stack, _);
    //@ ens true;
    {
        //@ open StackP(stack, ?vals);
        //@ assert (*stack).head |-> ?h;
        //@ close Nodes(h, vals);
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