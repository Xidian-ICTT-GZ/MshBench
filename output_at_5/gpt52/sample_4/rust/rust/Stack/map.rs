use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred nodes(n: *mut Node) =
    if n == std::ptr::null_mut() {
        true
    } else {
        (*n).next |-> ?nxt &*&
        (*n).value |-> ?v &*&
        alloc_block(n as *mut u8, Layout::new::<Node>()) &*&
        nodes(nxt)
    };

pred stack(s: *mut Stack) =
    (*s).head |-> ?h &*&
    alloc_block(s as *mut u8, Layout::new::<Stack>()) &*&
    nodes(h);

@*/

type I32Func = unsafe fn(*mut u8, i32) -> i32;

unsafe fn map_nodes(n: *mut Node, f: I32Func, data: *mut u8)
//@ req nodes(n);
//@ ens nodes(n);
{
    
    if !n.is_null() {
        //@ open nodes(n);
        let y = f(data, (*n).value);
        (*n).value = y;
        map_nodes((*n).next, f, data);
        //@ close nodes(n);
    }
    
}

unsafe fn dispose_nodes(n: *mut Node)
//@ req nodes(n);
//@ ens true;
{
    
    if !n.is_null() {
        //@ open nodes(n);
        dispose_nodes((*n).next);
        //@ open alloc_block(n as *mut u8, Layout::new::<Node>());
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
        
        
        //@ close nodes(std::ptr::null_mut());
        //@ close stack(stack);
        return stack;
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
    //@ req stack(stack) &*& (*stack).head |-> ?h &*& h != std::ptr::null_mut();
    //@ ens stack(stack);
    
    
    {
        
        //@ open stack(stack);
        //@ open nodes((*stack).head);
        let head = (*stack).head;
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ open alloc_block(head as *mut u8, Layout::new::<Node>());
        dealloc(head as *mut u8, Layout::new::<Node>());
        
        //@ close stack(stack);
        return result;
    }
    
    unsafe fn map(stack: *mut Stack, f: I32Func, data: *mut u8)
    //@ req stack(stack);
    //@ ens stack(stack);
    
    
    {
        
        //@ open stack(stack);
        map_nodes((*stack).head, f, data);
        //@ close stack(stack);
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack);
    //@ ens true;
    
    
    {
        
        //@ open stack(stack);
        dispose_nodes((*stack).head);
        //@ open alloc_block(stack as *mut u8, Layout::new::<Stack>());
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

unsafe fn plus_a(data: *mut u8, x: i32) -> i32
//@ req data != std::ptr::null_mut();
//@ ens true;

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