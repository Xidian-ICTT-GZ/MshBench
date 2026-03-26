//@ predicate Nodes(*mut Node n;);

//@ predicate Stack_pred(*mut Stack s;);

//@ predicate I32Func_pred(I32Func f;);

//@ fixpoint bool nodes_valid(*mut Node n) { return n == null || (nodes_valid((*n).next)); }

//@ lemma void nodes_valid_intro()
//@ requires true;
//@ ensures nodes_valid(null);
//@ {
//@ }

//@ lemma void nodes_valid_inductive(*mut Node n)
//@ requires n != null &*& Nodes((*n).next);
//@ ensures Nodes(n);
//@ {
//@ close Nodes(n);
//@ }

//@ lemma void nodes_valid_elim(*mut Node n)
//@ requires Nodes(n);
//@ ensures n == null || (n != null &*& Nodes((*n).next));
//@ {
//@ open Nodes(n);
//@ }

use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Func = unsafe fn(*mut u8, i32) -> i32;

unsafe fn map_nodes(n: *mut Node, f: I32Func, data: *mut u8)

{
    //@ open Nodes(n);
    if !n.is_null() {
        let y = f(data, (*n).value);
        (*n).value = y;
        map_nodes((*n).next, f, data);
    }
    //@ close Nodes(n);
    
}

unsafe fn dispose_nodes(n: *mut Node)

{
    //@ open Nodes(n);
    if !n.is_null() {
        dispose_nodes((*n).next);
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
        //@ close Stack_pred(stack);
        
        
        return stack;
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    
    
    {
        //@ open Stack_pred(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close Nodes(n);
        //@ close Stack_pred(stack);
        
        
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    
    
    {
        //@ open Stack_pred(stack);
        let head = (*stack).head;
        //@ open Nodes(head);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close Stack_pred(stack);
        
        return result;
    }
    
    unsafe fn map(stack: *mut Stack, f: I32Func, data: *mut u8)
    
    
    {
        //@ open Stack_pred(stack);
        map_nodes((*stack).head, f, data);
        //@ close Stack_pred(stack);
        
    }
    
    unsafe fn dispose(stack: *mut Stack)
    
    
    {
        //@ open Stack_pred(stack);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

unsafe fn plus_a(data: *mut u8, x: i32) -> i32

{
    
    let result = x + *(data as *mut i32);
    
    result
}

unsafe fn read_i32() -> i32

{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.parse().unwrap()
}

fn main()

{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::push(s, 30);
        let mut a = read_i32();
        

        
        Stack::map(s, plus_a, &raw mut a as *mut u8);
        
        Stack::dispose(s);
    }
}