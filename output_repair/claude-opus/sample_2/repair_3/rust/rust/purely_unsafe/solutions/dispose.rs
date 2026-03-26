use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@
predicate node_owned(n: *mut Node) =
    n != null ? (
        malloc_block_Node(n) *
        node_owned((*n).next)
    ) : emp;

predicate stack_owned(s: *mut Stack) =
    malloc_block_Stack(s) *
    node_owned((*s).head);
@*/

unsafe fn dispose_nodes(n: *mut Node)
    //@ requires node_owned(n);
    //@ ensures emp;
{
    if !n.is_null() {
        //@ open node_owned(n);
        let next = (*n).next;
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
        //@ ensures stack_owned(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack_owned(stack);
        return stack;
    }

    unsafe fn is_empty(stack: *mut Stack) -> bool
        //@ requires stack_owned(stack);
        //@ ensures stack_owned(stack);
    {
        //@ open stack_owned(stack);
        let head = (*stack).head;
        let result = head.is_null();
        //@ close stack_owned(stack);
        return result;
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        //@ requires stack_owned(stack);
        //@ ensures stack_owned(stack);
    {
        //@ open stack_owned(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close node_owned(n);
        //@ close stack_owned(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        //@ requires stack_owned(stack);
        //@ ensures stack_owned(stack);
    {
        //@ open stack_owned(stack);
        let head = (*stack).head;
        //@ open node_owned(head);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack_owned(stack);
        return result;
    }

    unsafe fn dispose(stack: *mut Stack)
        //@ requires stack_owned(stack);
        //@ ensures emp;
    {
        //@ open stack_owned(stack);
        dispose_nodes((*stack).head);
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