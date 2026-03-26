use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred node(p: *mut Node, next: *mut Node, value: i32) =
    alloc_block_Node(p) &*&
    p.next |-> next &*&
    p.value |-> value;

pred nodes(p: *mut Node) =
    p == std::ptr::null_mut() ?
        true
    :
        node(p, ?nxt, ?v) &*& nodes(nxt);

pred stack(s: *mut Stack) =
    alloc_block_Stack(s) &*&
    s.head |-> ?h &*&
    nodes(h);

@*/

impl Stack {

    //@ req true;
    //@ ens result != std::ptr::null_mut() &*& stack(result);
    unsafe fn create() -> *mut Stack
    
    
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(std::ptr::null_mut());
        //@ close stack(stack);
        
        
        stack
    }
    
    //@ req stack(stack);
    //@ ens stack(stack);
    unsafe fn push(stack: *mut Stack, value: i32)
    
    
    {
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ open stack(stack);
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close node(n, (*n).next, value);
        //@ close nodes(n);
        //@ close stack(stack);
        
        
    }
    
    //@ req stack(stack) &*& stack.head |-> ?h &*& h != std::ptr::null_mut();
    //@ ens stack(stack);
    unsafe fn pop(stack: *mut Stack) -> i32
    
    
    {
        
        //@ open stack(stack);
        let head = (*stack).head;
        
        //@ open nodes(head);
        //@ open node(head, ?nxt, ?v);
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ close stack(stack);
        dealloc(head as *mut u8, Layout::new::<Node>());
        
        result
    }

    //@ req stack(stack);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack)
    
    
    {
        
        //@ open stack(stack);
        
        
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

fn main()

{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        let result1 = Stack::pop(s);
        
        let result2 = Stack::pop(s);
        
        Stack::dispose(s);
    }
}