use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred Nodes(n: *mut Node;) =
    if n == 0 {
        true
    } else {
        (*n).next |-> ?next &*& (*n).value |-> ?v &*& alloc_block(n as *mut u8, Layout::new_::<Node>()) &*& struct_Node_padding(n) &*& Nodes(next)
    };

pred Stack(s: *mut Stack;) =
    (*s).head |-> ?head &*& alloc_block(s as *mut u8, Layout::new_::<Stack>()) &*& struct_Stack_padding(s) &*& Nodes(head);

pred StackNonEmpty(s: *mut Stack;) =
    (*s).head |-> ?head &*& alloc_block(s as *mut u8, Layout::new_::<Stack>()) &*& struct_Stack_padding(s) &*& head != 0 &*& (*head).next |-> ?next &*& (*head).value |-> ?v &*& alloc_block(head as *mut u8, Layout::new_::<Node>()) &*& struct_Node_padding(head) &*& Nodes(next);

lem Stack_to_StackNonEmpty(s: *mut Stack)
    req Stack(s) &*& (*s).head != 0;
    ens StackNonEmpty(s);
{
    open Stack(s);
    let head = (*s).head;
    open Nodes(head);
    close StackNonEmpty(s);
}

lem StackNonEmpty_to_Stack(s: *mut Stack)
    req StackNonEmpty(s);
    ens Stack(s);
{
    open StackNonEmpty(s);
    let head = (*s).head;
    let next = (*head).next;
    close Nodes(head);
    close Stack(s);
}

@*/

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens Stack(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close Nodes(0 as *mut Node);
        //@ close Stack(stack);
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req Stack(stack);
    //@ ens Stack(stack);
    {
        //@ open Stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close Nodes(n);
        //@ close Stack(stack);
    }
    
    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req StackNonEmpty(stack);
    //@ ens Stack(stack);
    {
        //@ open StackNonEmpty(stack);
        let head = (*stack).head;
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close Stack(stack);
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req (*stack).head |-> 0 &*& alloc_block(stack as *mut u8, Layout::new_::<Stack>()) &*& struct_Stack_padding(stack);
    //@ ens true;
    {
        
        
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
        //@ open Stack(s);
        //@ let h = (*s).head;
        //@ open Nodes(h);
        //@ close StackNonEmpty(s);
        let result1 = Stack::pop(s);
        //@ open Stack(s);
        //@ let h2 = (*s).head;
        //@ open Nodes(h2);
        //@ close StackNonEmpty(s);
        let result2 = Stack::pop(s);
        //@ open Stack(s);
        //@ open Nodes(0 as *mut Node);
        Stack::dispose(s);
    }
}