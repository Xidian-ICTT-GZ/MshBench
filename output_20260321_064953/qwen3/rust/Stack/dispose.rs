use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ pred nodes(*mut Node n;);

//@ pred stack(*mut Stack s;);

//@ pred node(*mut Node n, *mut Node next, i32 value) = 
//@   n as *mut u8 |-> ?b &*& struct_Node_padding(?next_, ?value_) &*& next_ == next &*& value_ == value &*&
//@   malloc_block_Node(n);

//@ pred stack_struct(*mut Stack s, *mut Node head) =
//@   s as *mut u8 |-> ?b &*& struct_Stack_padding(?head_) &*& head_ == head &*&
//@   malloc_block_Stack(s);

//@ lemma void nodes_nil()
//@ requires true;
//@ ensures nodes(null);
//@ { close nodes(null); }

//@ lemma void nodes_cons(*mut Node n)
//@ requires node(n, ?next, ?value) &*& nodes(next);
//@ ensures nodes(n);
//@ { close nodes(n); }

//@ lemma void nodes_unfold(*mut Node n)
//@ requires nodes(n);
//@ ensures n == null ? true : (node(n, ?next, ?value) &*& nodes(next));
//@ { open nodes(n); }

unsafe fn dispose_nodes(n: *mut Node)

{
    //@ open nodes(n);
    if !n.is_null() {
        //@ assert node(n, ?next, ?value) &*& nodes(next);
        dispose_nodes((*n).next);
        //@ open node(n, next, value);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
    //@ close nodes(null);
}

impl Stack {

    unsafe fn create() -> *mut Stack
    
    
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack_struct(stack, null);
        //@ close stack(stack);
        
        
        return stack;
    }
    
    unsafe fn is_empty(stack: *mut Stack) -> bool
    
    
    {
        //@ open stack(stack);
        //@ open stack_struct(stack, ?head);
        let head = (*stack).head;
        
        let result = (*stack).head.is_null();
        //@ close stack_struct(stack, head);
        //@ close stack(stack);
        
        
        return result;
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    
    
    {
        //@ open stack(stack);
        //@ open stack_struct(stack, ?old_head);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close node(n, old_head, value);
        (*stack).head = n;
        //@ close stack_struct(stack, n);
        //@ close stack(stack);
        
        
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    
    
    {
        //@ open stack(stack);
        //@ open stack_struct(stack, ?head);
        let head = (*stack).head;
        //@ assert head != null;
        //@ open node(head, ?next, ?value);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack_struct(stack, next);
        //@ close stack(stack);
        
        return result;
    }
    
    unsafe fn dispose(stack: *mut Stack)
    
    
    {
        //@ open stack(stack);
        //@ open stack_struct(stack, ?head);
        //@ close nodes(head);
        dispose_nodes((*stack).head);
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