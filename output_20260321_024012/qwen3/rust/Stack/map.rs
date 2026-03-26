//@ predicate Nodes(*mut Node; *mut Node) = true;

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
//@ req Nodes(n, _);
//@ ens Nodes(n, _);
{
    
    if !n.is_null() {
        let y = f(data, (*n).value);
        (*n).value = y;
        map_nodes((*n).next, f, data);
    }
    
}

unsafe fn dispose_nodes(n: *mut Node)
//@ req Nodes(n, _);
//@ ens true;
{
    
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens Stack(result, _);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        
        
        return stack;
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req Stack(stack, ?old_head) &*& Nodes(old_head, _);
    //@ ens Stack(stack, ?new_head) &*& Nodes(new_head, _) &*& new_head != old_head;
    {
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        
        
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req Stack(stack, ?old_head) &*& Nodes(old_head, _) &*& old_head != 0;
    //@ ens Stack(stack, ?new_head) &*& Nodes(new_head, _) &*& result == ?val;
    {
        
        let head = (*stack).head;
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        
        return result;
    }
    
    unsafe fn map(stack: *mut Stack, f: I32Func, data: *mut u8)
    //@ req Stack(stack, ?head) &*& Nodes(head, _) &*& data |-> ?d;
    //@ ens Stack(stack, head) &*& Nodes(head, _) &*& data |-> d;
    {
        
        map_nodes((*stack).head, f, data);
        
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req Stack(stack, ?head) &*& Nodes(head, _);
    //@ ens true;
    {
        
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

//@ predicate Stack(*mut Stack; *mut Node) = true;

unsafe fn plus_a(data: *mut u8, x: i32) -> i32
//@ req data |-> ?d;
//@ ens data |-> d &*& result == x + d;
{
    
    let result = x + *(data as *mut i32);
    
    result
}

unsafe fn read_i32() -> i32
//@ req true;
//@ ens true;
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.parse().unwrap()
}

fn main()
//@ req true;
//@ ens true;
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