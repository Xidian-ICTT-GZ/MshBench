use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@
pred node(n: *mut Node, next: *mut Node, value: i32) =
    alloc_block(n, std::mem::size_of::<Node>()) &*&
    struct_Node_padding(n) &*&
    (*n).next |-> next &*&
    (*n).value |-> value;
@*/

struct Node {
    next: *mut Node,
    value: i32,
}

/*@
pred stack_nodes(head: *mut Node) =
    head == std::ptr::null_mut() ?
        true
    :
        node(head, next, _) &*& stack_nodes(next);
        
pred stack(s: *mut Stack) =
    alloc_block(s, std::mem::size_of::<Stack>()) &*&
    struct_Stack_padding(s) &*&
    (*s).head |-> head &*&
    stack_nodes(head);
@*/

struct Stack {
    head: *mut Node,
}

impl Stack {
    //@ req true;
    //@ ens stack(result);
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack_nodes(std::ptr::null_mut());
        //@ close stack(stack);
        stack
    }
    
    //@ req stack(stack) &*& value == value;
    //@ ens stack(stack);
    unsafe fn push(stack: *mut Stack, value: i32) {
        //@ open stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close node(n, (*stack).head, value);
        //@ open stack_nodes((*stack).head);
        //@ close stack_nodes(n);
        (*stack).head = n;
        //@ close stack(stack);
    }
    
    //@ req stack(stack) &*& (*stack).head != std::ptr::null_mut();
    //@ ens stack(stack) &*& result == old_value;
    unsafe fn pop(stack: *mut Stack) -> i32 {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open stack_nodes(head);
        //@ open node(head, next, _);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack);
        result
    }
    
    //@ req stack(stack);
    //@ ens stack(stack);
    unsafe fn reverse(stack: *mut Stack) {
        //@ open stack(stack);
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        //@ close stack_nodes(m);
        //@ open stack_nodes(n);
        //@ inv stack_nodes(m) &*& stack_nodes(n);
        loop {
            if n.is_null() {
                break;
            }
            let next = (*n).next;
            //@ open stack_nodes(next);
            //@ open node(n, next, value);
            (*n).next = m;
            //@ close node(n, m, value);
            m = n;
            n = next;
            //@ close stack_nodes(m);
        }
        (*stack).head = m;
        //@ close stack(stack);
    }

    //@ req stack(stack);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack) {
        //@ open stack(stack);
        //@ open stack_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        let result1 = Stack::pop(s);
        let result2 = Stack::pop(s);
        Stack::dispose(s);
    }
}