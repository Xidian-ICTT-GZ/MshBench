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
        exists!(let v = ?; exists!(let next = ?; 
            node(n, v, next) &*& nodes(next)))
    }
}

#[predicate]
fn stack(s: *mut Stack) -> bool {
    unsafe {
        exists!(let head = ?; 
            (*s).head == head &*& nodes(head))
    }
}

#[predicate]
fn nodes_sum(n: *mut Node, sum: i32) -> bool {
    if n.is_null() {
        sum == 0
    } else {
        exists!(let v = ?; exists!(let next = ?; exists!(let subsum = ?;
            node(n, v, next) &*& nodes_sum(next, subsum) &*& sum == v + subsum)))
    }
}

#[predicate]
fn stack_sum(s: *mut Stack, sum: i32) -> bool {
    unsafe {
        exists!(let head = ?;
            (*s).head == head &*& nodes_sum(head, sum))
    }
}

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
    #[requires(nodes(nodes))]
    #[ensures(nodes(nodes) &*& nodes_sum(nodes, result))]
{
    let mut result = 0;
    
    if !nodes.is_null() {
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }
    
    result
}

impl Stack {
    unsafe fn create() -> *mut Stack
        #[ensures(stack(result))]
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }
    
    unsafe fn is_empty(stack: *mut Stack) -> bool
        #[requires(stack(stack))]
        #[ensures(stack(stack) &*& result == (*stack).head.is_null())]
    {
        let head = (*stack).head;
        let result = (*stack).head.is_null();
        result
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
        #[requires(stack(stack))]
        #[ensures(stack(stack) &*& stack_sum(stack, result))]
    {
        let result = get_nodes_sum((*stack).head);
        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        #[requires(stack(stack))]
        #[ensures(stack(stack))]
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        #[requires(stack(stack) &*& !(*stack).head.is_null())]
        #[ensures(stack(stack))]
    {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }
    
    unsafe fn popn(stack: *mut Stack, n: i32)
        #[requires(stack(stack))]
        #[ensures(stack(stack))]
    {
        let mut i = 0;
        loop {
            #[invariant(stack(stack) &*& i >= 0 &*& i <= n)]
            if i == n {
                break;
            }
            Stack::pop(stack);
            i += 1;
        }
    }
    
    unsafe fn dispose(stack: *mut Stack)
        #[requires(stack(stack))]
        #[ensures(true)]
    {
        let mut n = (*stack).head;
        loop {
            #[invariant(nodes(n))]
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