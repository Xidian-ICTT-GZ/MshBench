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
        alloc_block(n as *mut u8, Layout::new::<Node>()) &*&
        (*n).next |-> ?next &*&
        (*n).value |-> ?v &*&
        nodes(next)
    };

pred stack(s: *mut Stack) =
    alloc_block(s as *mut u8, Layout::new::<Stack>()) &*&
    (*s).head |-> ?h &*&
    nodes(h);

pred i32_cell(p: *mut i32; v: i32) =
    p |-> v;

@*/

type I32Func = unsafe fn(*mut u8, i32) -> i32;

//@ req nodes(n);
//@ ens nodes(n);
unsafe fn map_nodes(n: *mut Node, f: I32Func, data: *mut u8)

{
    
    if !n.is_null() {
        //@ open nodes(n);
        let y = f(data, (*n).value);
        (*n).value = y;
        map_nodes((*n).next, f, data);
        //@ close nodes(n);
    }
    
}

//@ req nodes(n);
//@ ens true;
unsafe fn dispose_nodes(n: *mut Node)

{
    
    if !n.is_null() {
        //@ open nodes(n);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {

    //@ req true;
    //@ ens stack(result);
    unsafe fn create() -> *mut Stack
    
    
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
    
    //@ req stack(stack);
    //@ ens stack(stack);
    unsafe fn push(stack: *mut Stack, value: i32)
    
    
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

    //@ req stack(stack) &*& (*stack).head |-> ?h &*& h != std::ptr::null_mut();
    //@ ens stack(stack);
    unsafe fn pop(stack: *mut Stack) -> i32
    
    
    {
        
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes(head);
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack);
        
        return result;
    }
    
    //@ req stack(stack);
    //@ ens stack(stack);
    unsafe fn map(stack: *mut Stack, f: I32Func, data: *mut u8)
    
    
    {
        
        //@ open stack(stack);
        map_nodes((*stack).head, f, data);
        //@ close stack(stack);
        
    }
    
    //@ req stack(stack);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack)
    
    
    {
        
        //@ open stack(stack);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

//@ req i32_cell(data as *mut i32, ?a);
//@ ens i32_cell(data as *mut i32, a) &*& result == x + a;
unsafe fn plus_a(data: *mut u8, x: i32) -> i32

{
    
    let result = x + *(data as *mut i32);
    
    result
}

//@ req true;
//@ ens true;
unsafe fn read_i32() -> i32

{
    //@ assume_correct
    let mut line = String::new();
    //@ assume_correct
    std::io::stdin().read_line(&mut line).unwrap();
    //@ assume_correct
    line.parse().unwrap()
}

fn main()

{
    unsafe {
        //@ close i32_cell(std::ptr::null_mut() as *mut i32, 0);
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::push(s, 30);
        let mut a = read_i32();
        
        //@ close i32_cell(&raw mut a as *mut i32, a);

        
        Stack::map(s, plus_a, &raw mut a as *mut u8);
        
        //@ open i32_cell(&raw mut a as *mut i32, _);
        Stack::dispose(s);
    }
}