use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[pred]
pub unsafe fn NodePred(n: *mut Node) -> bool {
    n != std::ptr::null_mut() &*&
    // Own the whole Node struct at pointer n
    std::ptr::valid(n, std::mem::size_of::<Node>()) &*&
    // The node's fields are accessible
    (*n).value |-> _ &*&
    (*n).next |-> _ 
}

#[pred]
pub unsafe fn NodesPred(mut n: *mut Node) -> bool {
    if n == std::ptr::null_mut() {
        true
    } else {
        NodePred(n) &*& NodesPred((*n).next)
    }
}

#[pred]
pub unsafe fn StackPred(s: *mut Stack) -> bool {
    s != std::ptr::null_mut() &*&
    std::ptr::valid(s, std::mem::size_of::<Stack>()) &*&
    (*s).head |-> _ &*&
    NodesPred((*s).head)
}

#[repr(C)]
pub struct Node {
    next: *mut Node,
    value: i32,
}

#[repr(C)]
pub struct Stack {
    head: *mut Node,
}

#[requires(nodes == std::ptr::null_mut() || NodePred(nodes))]
#[ensures(result == (
    if nodes == std::ptr::null_mut() { 0 } else { 
        let v = (*nodes).value;
        let next = (*nodes).next;
        v + get_nodes_sum(next)
    }
))]
pub unsafe fn get_nodes_sum(nodes: *mut Node) -> i32 {
    if nodes.is_null() {
        0
    } else {
        let sum = get_nodes_sum((*nodes).next);
        let v = (*nodes).value;
        v + sum
    }
}

impl Stack {
    #[requires(true)]
    #[ensures(result != std::ptr::null_mut() && StackPred(result))]
    pub unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack != std::ptr::null_mut() && StackPred(stack))]
    #[ensures(result == ((*stack).head == std::ptr::null_mut()) )]
    pub unsafe fn is_empty(stack: *mut Stack) -> bool {
        (*stack).head.is_null()
    }

    #[requires(stack != std::ptr::null_mut() && StackPred(stack))]
    #[ensures(result == get_nodes_sum((*stack).head))]
    pub unsafe fn get_sum(stack: *mut Stack) -> i32 {
        get_nodes_sum((*stack).head)
    }

    #[requires(stack != std::ptr::null_mut() && StackPred(stack))]
    #[ensures(StackPred(stack))]
    pub unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).value = value;
        (*n).next = (*stack).head;
        (*stack).head = n;
    }

    #[requires(stack != std::ptr::null_mut() && StackPred(stack) && (*stack).head != std::ptr::null_mut())]
    #[ensures(StackPred(stack) && result == old((*(*stack).head).value))]
    pub unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;
        let val = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        val
    }

    #[requires(stack != std::ptr::null_mut() && StackPred(stack))]
    #[ensures(true)]
    pub unsafe fn dispose(stack: *mut Stack) {
        let mut n = (*stack).head;
        #[invariant(
            StackPred(stack) &*&
            (n == std::ptr::null_mut() || NodePred(n))
        )]
        loop {
            if n.is_null() {
                break;
            }
            let next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
        }
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