use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@ pred node(p: *mut Node, next: *mut Node, value: i32) = 
    p != 0 &*& alloc_block_(p as *u8, std::mem::size_of::<Node>()) &*& 
    struct_Node_padding(p) &*&
    (*p).next |-> next &*& (*p).value |-> value;
@*/

/*@ pred stack(p: *mut Stack, head: *mut Node) = 
    p != 0 &*& alloc_block_(p as *u8, std::mem::size_of::<Stack>()) &*& 
    struct_Stack_padding(p) &*&
    (*p).head |-> head;
@*/

/*@ pred nodes(p: *mut Node) =
    p == 0 ? true :
    node(p, ?next, ?v) &*& nodes(next);
@*/

impl Stack {

    //@ req true;
    //@ ens stack(result, 0);
    unsafe fn create() -> *mut Stack
    
    
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close stack(stack, 0);
        (*stack).head = std::ptr::null_mut();
        
        
        stack
    }
    
    //@ req stack(stack, ?old_head) &*& nodes(old_head);
    //@ ens stack(stack, ?new_head) &*& nodes(new_head);
    unsafe fn push(stack: *mut Stack, value: i32)
    
    
    {
        //@ open stack(stack, old_head);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ close node(n, old_head, value);
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close stack(stack, n);
        
        
    }
    
    //@ req stack(stack, ?old_head) &*& old_head != 0 &*& nodes(old_head);
    //@ ens stack(stack, ?new_head) &*& nodes(new_head) &*& result == ?v &*& old_head == ?h &*& node(h, new_head, v);
    unsafe fn pop(stack: *mut Stack) -> i32
    
    
    {
        //@ open stack(stack, old_head);
        let head = (*stack).head;
        //@ open nodes(old_head);
        //@ assert node(head, ?next, ?v);
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ open node(head, next, v);
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, next);
        //@ close nodes(next);
        
        result
    }

    //@ req stack(stack, ?head) &*& nodes(head);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack)
    
    
    {
        //@ open stack(stack, _);
        //@ open nodes(?h);
        //@ while (h != 0) { open node(h, ?next, _); h = next; open nodes(next); }
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