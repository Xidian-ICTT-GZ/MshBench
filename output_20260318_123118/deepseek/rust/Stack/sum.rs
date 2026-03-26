use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn node(n: *mut Node, value: i32, next: *mut Node) -> bool {
    unsafe {
        (*n).value == value && (*n).next == next
    }
}

#[predicate]
fn nodes(n: *mut Node) -> bool {
    if n.is_null() {
        true
    } else {
        exists!(value: i32, next: *mut Node =>
            node(n, value, next) &*& nodes(next)
        )
    }
}

#[predicate]
fn stack(s: *mut Stack) -> bool {
    unsafe {
        exists!(head: *mut Node =>
            (*s).head == head &*& nodes(head)
        )
    }
}

#[predicate]
fn nodes_sum(n: *mut Node, sum: i32) -> bool {
    if n.is_null() {
        sum == 0
    } else {
        exists!(value: i32, next: *mut Node, sum_next: i32 =>
            node(n, value, next) &*& nodes_sum(next, sum_next) &*&
            sum == value + sum_next
        )
    }
}

#[lemma]
#[requires(nodes(n))]
#[ensures(exists!(sum: i32 => nodes_sum(n, sum)))]
fn nodes_sum_exists(n: *mut Node) {
    
}

#[requires(nodes(nodes_ptr))]
#[ensures(nodes_sum(nodes_ptr, result))]
unsafe fn get_nodes_sum(nodes_ptr: *mut Node) -> i32 {
    let mut result = 0;
    
    if !nodes_ptr.is_null() {
        result = get_nodes_sum((*nodes_ptr).next);
        result += (*nodes_ptr).value;
    }
    
    result
}

impl Stack {
    #[ensures(stack(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }
    
    #[requires(stack(stack))]
    #[ensures(stack(stack))]
    #[ensures(result == (*stack).head.is_null())]
    unsafe fn is_empty(stack: *mut Stack) -> bool {
        let head = (*stack).head;
        let result = (*stack).head.is_null();
        result
    }
    
    #[requires(stack(stack))]
    #[ensures(stack(stack))]
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        nodes_sum_exists((*stack).head);
        let result = get_nodes_sum((*stack).head);
        result
    }

    #[requires(stack(stack))]
    #[ensures(stack(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack(stack))]
    #[requires(!(*stack).head.is_null())]
    #[ensures(stack(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }
    
    #[requires(stack(stack))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        let mut n = (*stack).head;
        #[invariant(nodes(n))]
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