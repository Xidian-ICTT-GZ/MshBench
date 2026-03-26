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
pred stack(s: *mut Stack, head: *mut Node) =
    alloc_block(s, std::mem::size_of::<Stack>()) &*&
    struct_Stack_padding(s) &*&
    (*s).head |-> head;
    
pred lseg(start: *mut Node, end: *mut Node) =
    start == end ?
        true
    :
        node(start, ?next, ?value) &*& lseg(next, end);
@*/

struct Stack {
    head: *mut Node,
}

impl Stack {
    //@ req true;
    //@ ens stack(result, std::ptr::null_mut());
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack, std::ptr::null_mut());
        stack
    }
    
    //@ req stack(stack, ?head);
    //@ ens stack(stack, ?new_head) &*& node(new_head, head, value);
    unsafe fn push(stack: *mut Stack, value: i32) {
        //@ open stack(stack, head);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close node(n, head, value);
        //@ close stack(stack, n);
    }
    
    //@ req stack(stack, ?head) &*& head != std::ptr::null_mut() &*& node(head, ?next, ?value);
    //@ ens stack(stack, next) &*& result == value;
    unsafe fn pop(stack: *mut Stack) -> i32 {
        //@ open stack(stack, head);
        //@ open node(head, next, ?v);
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, next);
        result
    }
    
    //@ req stack(stack, ?head);
    //@ ens stack(stack, ?rev_head) &*& lseg(rev_head, std::ptr::null_mut());
    unsafe fn reverse(stack: *mut Stack) {
        //@ open stack(stack, head);
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        //@ close lseg(std::ptr::null_mut(), std::ptr::null_mut());
        //@ let mut prev = std::ptr::null_mut();
        
        loop {
            //@ inv lseg(m, std::ptr::null_mut()) &*& lseg(n, std::ptr::null_mut());
            if n.is_null() {
                break;
            }
            let next = (*n).next;
            //@ open lseg(n, std::ptr::null_mut());
            //@ assert node(n, next, ?value);
            (*n).next = m;
            m = n;
            n = next;
            //@ close lseg(m, std::ptr::null_mut());
        }
        
        (*stack).head = m;
        //@ close stack(stack, m);
    }

    //@ req stack(stack, std::ptr::null_mut());
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack) {
        //@ open stack(stack, std::ptr::null_mut());
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        let result1 = Stack::pop(s);
        //@ assert result1 == 20;
        let result2 = Stack::pop(s);
        //@ assert result2 == 10;
        Stack::dispose(s);
    }
}