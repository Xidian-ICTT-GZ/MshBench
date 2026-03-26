use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ pred node_list(n: *mut Node) = if n == std::ptr::null_mut() { true } else { (*n).next |-> ?next &*& (*n).value |-> ?v &*& std::alloc::alloc_block(n as *mut u8, Layout::new::<Node>()) &*& node_list(next) };
//@ pred stack(s: *mut Stack) = (*s).head |-> ?h &*& std::alloc::alloc_block(s as *mut u8, Layout::new::<Stack>()) &*& node_list(h);

//@ pred i32_ptr(p: *mut i32; v: i32) = *p |-> v;
//@ pred u8_i32(data: *mut u8; v: i32) = i32_ptr(data as *mut i32, v);

type I32Func = unsafe fn(*mut u8, i32) -> i32;

unsafe fn map_nodes(n: *mut Node, f: I32Func, data: *mut u8)
//@ req node_list(n);
//@ ens node_list(n);
{
    
    if !n.is_null() {
        //@ open node_list(n);
        let y = f(data, (*n).value);
        (*n).value = y;
        map_nodes((*n).next, f, data);
        //@ close node_list(n);
    }
    
}

unsafe fn dispose_nodes(n: *mut Node)
//@ req node_list(n);
//@ ens true;
{
    
    if !n.is_null() {
        //@ open node_list(n);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
        //@ open std::alloc::alloc_block(n as *mut u8, Layout::new::<Node>());
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
        //@ close std::alloc::alloc_block(stack as *mut u8, Layout::new::<Stack>());
        (*stack).head = std::ptr::null_mut();
        //@ close node_list(std::ptr::null_mut());
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
        //@ close std::alloc::alloc_block(n as *mut u8, Layout::new::<Node>());
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close node_list(n);
        (*stack).head = n;
        //@ close stack(stack);
        
        
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack) &*& (*stack).head |-> ?h &*& h != std::ptr::null_mut();
    //@ ens stack(stack);
    {
        
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open node_list(head);
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ open std::alloc::alloc_block(head as *mut u8, Layout::new::<Node>());
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
        dealloc(stack as *mut u8, Layout::new::<Stack>());
        //@ open std::alloc::alloc_block(stack as *mut u8, Layout::new::<Stack>());
    }

}

unsafe fn plus_a(data: *mut u8, x: i32) -> i32
//@ req u8_i32(data, ?a);
//@ ens u8_i32(data, a) &*& result == x + a;
{
    
    //@ open u8_i32(data, a);
    let result = x + *(data as *mut i32);
    //@ close u8_i32(data, a);
    
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
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::push(s, 30);
        let mut a = read_i32();
        
        //@ close i32_ptr(&raw mut a, a);
        //@ close u8_i32((&raw mut a) as *mut u8, a);
        Stack::map(s, plus_a, &raw mut a as *mut u8);
        //@ open u8_i32((&raw mut a) as *mut u8, _);
        //@ open i32_ptr(&raw mut a, _);
        
        Stack::dispose(s);
    }
}