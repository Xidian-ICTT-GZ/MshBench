//@ req true;
//@ ens true;
use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@ pred node(p: *mut Node, next: *mut Node, value: i32) =
    alloc_block(p as *mut u8, Layout::new::<Node>()) &*&
    struct_Node_padding(p) &*&
    (*p).next |-> next &*&
    (*p).value |-> value;
@*/

/*@ pred nodes(p: *mut Node) =
    p == std::ptr::null_mut() ?
        true
    :
        node(p, ?next, ?value) &*& nodes(next);
@*/

/*@ pred stack(s: *mut Stack) =
    alloc_block(s as *mut u8, Layout::new::<Stack>()) &*&
    struct_Stack_padding(s) &*&
    (*s).head |-> ?head &*&
    nodes(head);
@*/

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Func = unsafe fn(*mut u8, i32) -> i32;

//@ req nodes(n) &*& [?f]lifetime_token(?t) &*& is_I32Func(f, t, ?F);
//@ ens nodes(n) &*& [f]lifetime_token(t) &*& is_I32Func(f, t, F);
unsafe fn map_nodes(n: *mut Node, f: I32Func, data: *mut u8)

{
    
    if !n.is_null() {
        //@ open nodes(n);
        //@ open node(n, _, _);
        let y = f(data, (*n).value);
        (*n).value = y;
        //@ close node(n, (*n).next, y);
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
        //@ open node(n, _, _);
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
    
    //@ req stack(stack) &*& [?f]lifetime_token(?t) &*& is_I32Func(?dummy_f, t, ?F);
    //@ ens stack(stack) &*& [f]lifetime_token(t) &*& is_I32Func(dummy_f, t, F);
    unsafe fn push(stack: *mut Stack, value: i32)
    
    
    {
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ open stack(stack);
        let old_head = (*stack).head;
        (*n).next = old_head;
        (*n).value = value;
        (*stack).head = n;
        //@ close node(n, old_head, value);
        //@ close nodes(n);
        //@ close stack(stack);
        
        
    }

    //@ req stack(stack) &*& (*stack).head != std::ptr::null_mut();
    //@ ens stack(stack) &*& result == old((*stack).head).value;
    unsafe fn pop(stack: *mut Stack) -> i32
    
    
    {
        
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes(head);
        //@ open node(head, _, _);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close nodes((*stack).head);
        //@ close stack(stack);
        
        return result;
    }
    
    //@ req stack(stack) &*& [?f]lifetime_token(?t) &*& is_I32Func(f, t, ?F);
    //@ ens stack(stack) &*& [f]lifetime_token(t) &*& is_I32Func(f, t, F);
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

//@ req [?f]lifetime_token(?t) &*& *data == ?a;
//@ ens [f]lifetime_token(t) &*& *data == a &*& result == a + x;
unsafe fn plus_a(data: *mut u8, x: i32) -> i32

{
    
    let result = x + *(data as *mut i32);
    
    result
}

//@ assume_correct
unsafe fn read_i32() -> i32

{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.parse().unwrap()
}

//@ req true;
//@ ens true;
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