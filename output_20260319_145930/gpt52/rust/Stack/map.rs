use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred node_list(n: *mut Node) =
    n == 0 ?
        true
    :
        alloc_block(n as *mut u8, Layout::new::<Node>()) &*&
        (*n).next |-> ?next &*&
        (*n).value |-> ?v &*&
        node_list(next);

pred stack(s: *mut Stack) =
    alloc_block(s as *mut u8, Layout::new::<Stack>()) &*&
    (*s).head |-> ?h &*&
    node_list(h);

@*/

type I32Func = unsafe fn(*mut u8, i32) -> i32;

//@ req node_list(n);
//@ ens node_list(n);
unsafe fn map_nodes(n: *mut Node, f: I32Func, data: *mut u8)

{
    
    if !n.is_null() {
        //@ open node_list(n);
        let y = f(data, (*n).value);
        (*n).value = y;
        map_nodes((*n).next, f, data);
        //@ close node_list(n);
    }
    
}

//@ req node_list(n);
//@ ens true;
unsafe fn dispose_nodes(n: *mut Node)

{
    
    if !n.is_null() {
        //@ open node_list(n);
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
        
        //@ close node_list(0);
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
        
        //@ close node_list(n);
        //@ close stack(stack);
        
    }

    //@ req stack(stack) &*& (*stack).head |-> ?h &*& h != 0;
    //@ ens stack(stack);
    unsafe fn pop(stack: *mut Stack) -> i32
    
    
    {
        
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open node_list(head);
        
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

//@ req true;
//@ ens true;
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
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::push(s, 30);
        let mut a = read_i32();
        

        
        Stack::map(s, plus_a, &raw mut a as *mut u8);
        
        Stack::dispose(s);
    }
}