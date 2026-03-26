use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@ pred stack(*mut Stack, *mut Node) = 
    alloc_block_Stack(s) &*& struct_Stack_padding(s) &*&
    (*s).head |-> head &*& nodes(head); @*/

/*@ pred nodes(*mut Node) =
    match n {
        null => true,
        _ => alloc_block_Node(n) &*& struct_Node_padding(n) &*&
             (*n).value |-> _ &*& (*n).next |-> next &*& nodes(next)
    }; @*/

impl Stack {

    //@ req true;
    //@ ens stack(result, null);
    unsafe fn create() -> *mut Stack
    
    
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close alloc_block_Stack(stack)();
        //@ close struct_Stack_padding(stack)();
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(null)();
        //@ close stack(stack, null);
        
        
        stack
    }
    
    //@ req stack(stack, old_head) &*& nodes(new_nodes) &*& new_nodes == n &*& n != null &*&
    
    //@ ens stack(stack, n);
    unsafe fn push(stack: *mut Stack, value: i32)
    
    
    {
        //@ open stack(stack, _);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ close alloc_block_Node(n)();
        //@ close struct_Node_padding(n)();
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close nodes(n);
        //@ close stack(stack, n);
        
        
    }
    
    //@ req stack(stack, head) &*& head != null &*& nodes(head);
    //@ ens stack(stack, next) &*& nodes(next) &*& result == v &*&
    
    unsafe fn pop(stack: *mut Stack) -> i32
    
    
    {
        //@ open stack(stack, _);
        //@ open nodes(_);
        let head = (*stack).head;
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ open alloc_block_Node(head)();
        //@ open struct_Node_padding(head)();
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, (*stack).head);
        
        
        result
    }

    //@ req stack(stack, _);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack)
    
    
    {
        //@ open stack(stack, _);
        //@ open alloc_block_Stack(stack)();
        //@ open struct_Stack_padding(stack)();
        
        
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