use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Predicate = unsafe fn(i32) -> bool;

predicate node_pred(*mut Node n; *mut Node next, i32 value) =
    n as *mut u8 |-> _ &*&
    struct_Node_padding(n) &*&
    (*n).next |-> next &*&
    (*n).value |-> value;

predicate node_list(*mut Node n;) =
    if n == std::ptr::null_mut() {
        emp
    } else {
        exists(*mut Node next, i32 value) {
            node_pred(n, next, value) * node_list(next)
        }
    };

predicate stack_pred(*mut Stack s;) =
    s |-> ?head &*& node_list(head);

unsafe fn filter_nodes(n: *mut Node, p: I32Predicate) -> *mut Node
    requires node_list(n);
    ensures node_list(result);
{
    if n.is_null() {
        std::ptr::null_mut()
    } else {
        open node_list(n);
        let v = *(*n).value;
        let keep = p(v);
        let next_ptr = *(*n).next;
        if keep {
            let filtered_next = filter_nodes(next_ptr, p);
            *(*n).next = filtered_next;
            close node_pred(n, filtered_next, v);
            close node_list(n);
            n
        } else {
            dealloc(n as *mut u8, Layout::new::<Node>());
            let result = filter_nodes(next_ptr, p);
            result
        }
    }
}

unsafe fn dispose_nodes(n: *mut Node)
    requires node_list(n);
    ensures emp;
{
    if !n.is_null() {
        open node_list(n);
        let next = *(*n).next;
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
        requires emp;
        ensures stack_pred(result);
    {
        let layout = Layout::new::<Stack>();
        let stack = alloc(layout) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(layout);
        }
        (*stack).head = std::ptr::null_mut();
        close node_list(std::ptr::null_mut());
        close stack_pred(stack);
        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        requires stack_pred(stack);
        ensures stack_pred(stack);
    {
        open stack_pred(stack);
        let old_head = *(*stack).head;
        let layout = Layout::new::<Node>();
        let n = alloc(layout) as *mut Node;
        if n.is_null() {
            handle_alloc_error(layout);
        }
        (*n).next = old_head;
        (*n).value = value;
        close node_pred(n, old_head, value);
        close node_list(n);
        (*stack).head = n;
        close stack_pred(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        requires stack_pred(stack);
        ensures stack_pred(stack);
    {
        open stack_pred(stack);
        let head = (*stack).head;
        open node_list(head);
        let next = *(*head).next;
        let result = *(*head).value;
        (*stack).head = next;
        close node_list(next);
        close stack_pred(stack);
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
        requires stack_pred(stack);
        ensures stack_pred(stack);
    {
        open stack_pred(stack);
        let head = (*stack).head;
        let new_head = filter_nodes(head, p);
        (*stack).head = new_head;
        close stack_pred(stack);
    }

    unsafe fn dispose(stack: *mut Stack)
        requires stack_pred(stack);
        ensures emp;
    {
        open stack_pred(stack);
        let head = (*stack).head;
        dispose_nodes(head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

unsafe fn neq_20(x: i32) -> bool {
    x != 20
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}