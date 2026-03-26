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
    if n == 0 {
        true
    } else {
        malloc_block_Node(n) &*&
        (*n).next |-> ?nx &*&
        (*n).value |-> ?v &*&
        nodes(nx)
    };

pred stack(s: *mut Stack) =
    malloc_block_Stack(s) &*&
    (*s).head |-> ?h &*& nodes(h);

@*/

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req nodes(nodes);
//@ ens nodes(nodes);
{
    let mut result = 0;
    
    if !nodes.is_null() {
        //@ open nodes(nodes);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close nodes(nodes);
    }
    
    result
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens result != 0 &*& stack(result);
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
    
    unsafe fn is_empty(stack: *mut Stack) -> bool
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let head = (*stack).head;
        
        let result = (*stack).head.is_null();
        
        //@ close stack(stack);
        result
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let result = get_nodes_sum((*stack).head);
        //@ close stack(stack);
        
        result
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
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ close stack(stack);
        //@ assert malloc_block_Node(head);
        //@ assert (*head).next |-> _ &*& (*head).value |-> _;
        dealloc(head as *mut u8, Layout::new::<Node>());
        
        result
    }
    
    unsafe fn popn(stack: *mut Stack, n: i32)
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        let mut i = 0;
        loop {
            //@ inv stack(stack);
            
            if i == n {
                break;
            }
            Stack::pop(stack);
            i += 1;
        }
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack);
    //@ ens true;
    {
        //@ open stack(stack);
        let mut n = (*stack).head;
        loop {
            //@ inv nodes(n);
            
            if n.is_null() {
                break;
            }
            
            //@ open nodes(n);
            let next = (*n).next;
            //@ assert malloc_block_Node(n);
            //@ assert (*n).next |-> _ &*& (*n).value |-> _;
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
        }
        
        //@ assert malloc_block_Stack(stack);
        //@ assert (*stack).head |-> _;
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

fn main()

{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}