use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate node_list(*mut Node n;) = 
    if n == std::ptr::null_mut() { 
        emp 
    } else { 
        (*n).next |-> ?next &*& (*n).value |-> _ &*& node_list(next) 
    };

predicate stack_inv(*mut Stack s) = 
    (*s).head |-> ?head &*& node_list(head);

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
    requires node_list(nodes),
    ensures node_list(nodes);
{
    let mut result = 0;

    if nodes != std::ptr::null_mut() {
        open node_list(nodes);
        let next = (*nodes).next;
        result = get_nodes_sum(next);
        close node_list(nodes);
        result += (*nodes).value;
    }

    result
}

impl Stack {
    unsafe fn create() -> *mut Stack
        requires true,
        ensures stack_inv(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        close stack_inv(stack);
        stack
    }

    unsafe fn is_empty(stack: *mut Stack) -> bool
        requires stack_inv(stack),
        ensures stack_inv(stack);
    {
        open stack_inv(stack);
        let head = (*stack).head;
        close stack_inv(stack);
        head == std::ptr::null_mut()
    }

    unsafe fn get_sum(stack: *mut Stack) -> i32
        requires stack_inv(stack),
        ensures stack_inv(stack);
    {
        open stack_inv(stack);
        let head = (*stack).head;
        let result = get_nodes_sum(head);
        close stack_inv(stack);
        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        requires stack_inv(stack),
        ensures stack_inv(stack);
    {
        open stack_inv(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        close stack_inv(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        requires stack_inv(stack),
        ensures stack_inv(stack);
    {
        open stack_inv(stack);
        let head = (*stack).head;
        assert(head != std::ptr::null_mut());
        open node_list(head);
        let next = (*head).next;
        let result = (*head).value;
        (*stack).head = next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        close stack_inv(stack);
        result
    }

    unsafe fn popn(stack: *mut Stack, n: i32)
        requires stack_inv(stack) &*& n >= 0,
        ensures stack_inv(stack);
    {
        let mut i = 0;
        loop
            invariant stack_inv(stack) &*& 0 <= i &*& i <= n;
        {
            if i == n {
                break;
            }
            Stack::pop(stack);
            i += 1;
        }
    }

    unsafe fn dispose(stack: *mut Stack)
        requires stack_inv(stack),
        ensures emp;
    {
        open stack_inv(stack);
        let mut n = (*stack).head;
        while n != std::ptr::null_mut()
            invariant node_list(n) &*& (*stack).head |-> n;
        {
            open node_list(n);
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