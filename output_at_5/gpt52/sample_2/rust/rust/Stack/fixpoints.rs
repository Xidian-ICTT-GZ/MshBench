use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred node(n: *mut Node; next: *mut Node, value: i32) =
    n != 0 &*&
    struct_Node_padding(n) &*&
    (*n).next |-> next &*&
    (*n).value |-> value;

pred nodes(h: *mut Node) =
    h == 0 ?
        true
    :
        node(h, ?nxt, ?v) &*& nodes(nxt);

pred stack(s: *mut Stack) =
    s != 0 &*&
    struct_Stack_padding(s) &*&
    (*s).head |-> ?h &*&
    nodes(h);

@*/

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
        //@ close nodes(0);
        //@ close stack(stack);
        
        
        stack
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
        //@ close node(n, (*stack).head, value);
        //@ close nodes((*stack).head);
        //@ close nodes(n);
        (*stack).head = n;
        
        //@ close stack(stack);
        
        
    }
    
    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack) &*& (*stack).head |-> ?h &*& h != 0;
    //@ ens stack(stack);
    
    
    {
        //@ open stack(stack);
        
        let head = (*stack).head;
        //@ open nodes(head);
        //@ open node(head, ?nxt, ?v);
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        
        dealloc(head as *mut u8, Layout::new::<Node>());
        
        //@ close stack(stack);
        
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack);
    //@ ens true;
    
    
    {
        //@ open stack(stack);
        //@ open nodes((*stack).head);
        //@ leak nodes((*stack).head);
        //@ leak (*stack).head |-> _;
        //@ leak struct_Stack_padding(stack);
        
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