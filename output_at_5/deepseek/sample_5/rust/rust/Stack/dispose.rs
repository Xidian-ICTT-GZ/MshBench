use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@
predicate nodes(n: *mut Node) =
    n == 0 ?
        true
    :
        malloc_block_Node(n) &*&
        struct_Node_padding(n) &*&
        (*n).next |-> ?next &*&
        (*n).value |-> ?val &*&
        nodes(next);
@*/

/*@
predicate stack(stack: *mut Stack) =
    malloc_block_Stack(stack) &*&
    struct_Stack_padding(stack) &*&
    (*stack).head |-> ?head &*&
    nodes(head);
@*/

unsafe fn dispose_nodes(n: *mut Node)
//@ req nodes(n);
//@ ens true;
{
    
    if !n.is_null() {
        //@ open nodes(n);
        dispose_nodes((*n).next);
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
    
    unsafe fn is_empty(stack: *mut Stack) -> bool
    //@ req stack(stack);
    //@ ens stack(stack) &*& result == ((*stack).head == 0);
    {
        
        //@ open stack(stack);
        let head = (*stack).head;
        
        let result = (*stack).head.is_null();
        //@ close stack(stack);
        
        return result;
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
    //@ req stack(stack) &*& (*stack).head != 0;
    //@ ens stack(stack);
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
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack);
    //@ ens true;
    {
        
        //@ open stack(stack);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

fn main()
//@ req true;
//@ ens true;
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