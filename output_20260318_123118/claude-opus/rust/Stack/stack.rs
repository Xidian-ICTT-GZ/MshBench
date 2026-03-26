use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred Nodes(node: *mut Node;) =
    if node == 0 {
        true
    } else {
        (*node).next |-> ?next &*& (*node).value |-> ?v &*& alloc_block(node as *mut u8, Layout::new_::<Node>()) &*& struct_Node_padding(node) &*& Nodes(next)
    };

pred Stack(stack: *mut Stack;) =
    (*stack).head |-> ?head &*& alloc_block(stack as *mut u8, Layout::new_::<Stack>()) &*& struct_Stack_padding(stack) &*& Nodes(head);

pred StackNonEmpty(stack: *mut Stack;) =
    (*stack).head |-> ?head &*& alloc_block(stack as *mut u8, Layout::new_::<Stack>()) &*& struct_Stack_padding(stack) &*& head != 0 &*& (*head).next |-> ?next &*& (*head).value |-> ?v &*& alloc_block(head as *mut u8, Layout::new_::<Node>()) &*& struct_Node_padding(head) &*& Nodes(next);

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
        //@ open Nodes(head);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close Stack(stack);
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req (*stack).head |-> 0 &*& alloc_block(stack as *mut u8, Layout::new_::<Stack>()) &*& struct_Stack_padding(stack) &*& Nodes(0 as *mut Node);
    //@ ens true;
    {
        //@ open Nodes(0 as *mut Node);
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
        //@ open Nodes((*s).head);
        //@ close StackNonEmpty(s);
        Stack::pop(s);
        //@ open Stack(s);
        //@ open Nodes((*s).head);
        //@ close StackNonEmpty(s);
        Stack::pop(s);
        //@ open Stack(s);
        Stack::dispose(s);
    }
}