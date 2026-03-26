use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate node_list(*mut Node n;);

predicate stack_inv(*mut Stack s;) = 
    s != null_mut() &*&
    [_]s as *mut u8 |-> ?layout &*& layout == Layout::new::<Stack>() &*&
    struct_Stack_padding(s) &*&
    (*s).head |-> ?head &*&
    node_list(head);

predicate node_list(null_mut()) = true;
predicate node_list(*mut Node n) =
    n != null_mut() &*&
    [_]n as *mut u8 |-> ?layout &*& layout == Layout::new::<Node>() &*&
    struct_Node_padding(n) &*&
    (*n).next |-> ?next &*&
    (*n).value |-> _ &*&
    node_list(next);

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
    requires node_list(nodes),
    ensures node_list(nodes) &*& result == ?sum;
{
    let mut result = 0;

    if !nodes.is_null() {
        let next = (*nodes).next;
        open node_list(nodes);
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
        let layout = Layout::new::<Stack>();
        let stack = alloc(layout) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(layout);
        }
        (*stack).head = std::ptr::null_mut();
        close stack_inv(stack);
        stack
    }

    unsafe fn is_empty(stack: *mut Stack) -> bool
        requires stack_inv(stack),
        ensures stack_inv(stack) &*& result == ((*stack).head == null_mut());
    {
        let result = (*stack).head.is_null();
        result
    }

    unsafe fn get_sum(stack: *mut Stack) -> i32
        requires stack_inv(stack),
        ensures stack_inv(stack) &*& result == ?sum;
    {
        open stack_inv(stack);
        let head = (*stack).head;
        let sum = get_nodes_sum(head);
        close stack_inv(stack);
        sum
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        requires stack_inv(stack),
        ensures stack_inv(stack);
    {
        open stack_inv(stack);
        let layout = Layout::new::<Node>();
        let n = alloc(layout) as *mut Node;
        if n.is_null() {
            handle_alloc_error(layout);
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        close stack_inv(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        requires stack_inv(stack) &*& (*stack).head != null_mut(),
        ensures stack_inv(stack) &*& result == ?val;
    {
        open stack_inv(stack);
        let head = (*stack).head;
        open node_list(head);
        let val = (*head).value;
        let next = (*head).next;
        (*stack).head = next;
        let layout = Layout::new::<Node>();
        dealloc(head as *mut u8, layout);
        close stack_inv(stack);
        val
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
            let head = (*stack).head;
            if head.is_null() {
                break;
            }
            Stack::pop(stack);
            i += 1;
        }
    }

    unsafe fn dispose(stack: *mut Stack)
        requires stack_inv(stack),
        ensures true;
    {
        open stack_inv(stack);
        let mut n = (*stack).head;
        while n != null_mut()
            invariant node_list(n);
        {
            open node_list(n);
            let next = (*n).next;
            let layout = Layout::new::<Node>();
            dealloc(n as *mut u8, layout);
            n = next;
        }
        let layout = Layout::new::<Stack>();
        dealloc(stack as *mut u8, layout);
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