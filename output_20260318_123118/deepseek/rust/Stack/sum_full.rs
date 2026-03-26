use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn nodes(n: *mut Node) -> bool {
    if n.is_null() {
        true
    } else {
        exists!((next: *mut Node, v: i32) => (*n).next |-> next && (*n).value |-> v && nodes(next))
    }
}

#[predicate]
fn stack(s: *mut Stack) -> bool {
    exists!((head: *mut Node) => (*s).head |-> head && nodes(head))
}

#[predicate]
fn nodes_sum(n: *mut Node, s: i32) -> bool {
    if n.is_null() {
        s == 0
    } else {
        exists!((next: *mut Node, v: i32, tail_sum: i32) => 
            (*n).next |-> next && (*n).value |-> v && 
            nodes_sum(next, tail_sum) && s == v + tail_sum)
    }
}

#[requires(nodes(node))]
#[ensures(nodes(node))]
#[ensures(result == old(get_nodes_sum_spec(node)))]
unsafe fn get_nodes_sum(node: *mut Node) -> i32
{
    let mut result = 0;
    if !node.is_null() {
        #[invariant(nodes(node))]
        #[invariant((*node).next |-> ?next && (*node).value |-> ?v)]
        #[invariant(nodes(next))]
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
    }
    result
}

#[logic]
fn get_nodes_sum_spec(node: *mut Node) -> i32 {
    if node.is_null() {
        0
    } else {
        (*node).value + get_nodes_sum_spec((*node).next)
    }
}

impl Stack {
    #[ensures(stack(result))]
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }
    
    #[requires(stack(stack))]
    #[ensures(stack(stack))]
    #[ensures(result == old(get_nodes_sum_spec((*stack).head)))]
    unsafe fn get_sum(stack: *mut Stack) -> i32
    {
        let result = get_nodes_sum((*stack).head);
        result
    }
    
    #[requires(stack(stack))]
    #[ensures(stack(stack))]
    unsafe fn push(stack: *mut Stack, value: i32)
    {
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
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    #[requires(stack(stack))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack)
    {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main()
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        let sum = Stack::get_sum(s);
        let result1 = Stack::pop(s);
        let result2 = Stack::pop(s);
        Stack::dispose(s);
    }
}