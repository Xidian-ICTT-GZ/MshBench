use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

/*@
pred Node_own(node: *mut Node; next: *mut Node, value: i32) =
    (*node).next |-> next &*& (*node).value |-> value &*&
    struct_Node_padding(node);

pred Nodes(head: *mut Node;) =
    if head == std::ptr::null_mut() {
        true
    } else {
        Node_own(head, ?next, ?value) &*& alloc_block(head as *mut u8, Layout::new_::<Node>()) &*& Nodes(next)
    };

pred Stack_own(stack: *mut Stack; head: *mut Node) =
    (*stack).head |-> head &*& struct_Stack_padding(stack);

pred StackFull(stack: *mut Stack;) =
    stack != std::ptr::null_mut() &*&
    alloc_block(stack as *mut u8, Layout::new_::<Stack>()) &*&
    Stack_own(stack, ?head) &*&
    Nodes(head);
@*/

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req Layout::new_::<Stack>().size() > 0 &*& Layout::new_::<Stack>().align() > 0;
    //@ ens StackFull(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close Nodes(std::ptr::null_mut());
        (*stack).head = std::ptr::null_mut();
        //@ close Stack_own(stack, std::ptr::null_mut());
        //@ close StackFull(stack);
        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req StackFull(stack);
    //@ ens StackFull(stack);
    {
        //@ open StackFull(stack);
        //@ open Stack_own(stack, ?old_head);
        let old_head = (*stack).head;
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = old_head;
        (*n).value = value;
        //@ close Node_own(n, old_head, value);
        //@ close Nodes(n);
        (*stack).head = n;
        //@ close Stack_own(stack, n);
        //@ close StackFull(stack);
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req StackFull(stack);
    //@ ens true;
    {
        //@ open StackFull(stack);
        //@ open Stack_own(stack, ?head);
        let head = (*stack).head;
        let mut current = head;
        //@ close Nodes(current);
        //@ open Nodes(current);
        while current != std::ptr::null_mut()
        //@ inv Nodes(current);
        {
            //@ open Nodes(current);
            //@ open Node_own(current, ?next, ?v);
            let next = (*current).next;
            dealloc(current as *mut u8, Layout::new::<Node>());
            current = next;
        }
        //@ open Nodes(current);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}