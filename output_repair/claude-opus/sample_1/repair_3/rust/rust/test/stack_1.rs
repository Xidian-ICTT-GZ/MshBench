use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

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

pred StackInv(s: *mut Stack;) =
    alloc_block(s as *mut u8, Layout::new_::<Stack>()) &*& struct_Stack_padding(s) &*& (*s).head |-> ?head &*& Nodes(head);
@*/

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req true
    //@ ens StackInv(result)
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close Nodes(0 as *mut Node);
        (*stack).head = std::ptr::null_mut();
        //@ close StackInv(stack);
        stack
    }
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req StackInv(stack)
    //@ ens StackInv(stack)
    {
        //@ open StackInv(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close Nodes(n);
        (*stack).head = n;
        //@ close StackInv(stack);
    }
    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req StackInv(stack) &*& (*stack).head != 0
    //@ ens StackInv(stack)
    {
        //@ open StackInv(stack);
        let head = (*stack).head;
        //@ open Nodes(head);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close StackInv(stack);
        result
    }
    unsafe fn dispose(stack: *mut Stack)
    //@ req StackInv(stack) &*& (*stack).head == 0
    //@ ens true
    {
        //@ open StackInv(stack);
        //@ open Nodes(0 as *mut Node);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}
fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}