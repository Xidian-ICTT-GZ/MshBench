use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@
predicate nodes(*mut Node n) =
    n == null ? true :
    n->value |-> _ &*& n->next |-> ?next &*& nodes(next);

predicate stack(*mut Stack s) =
    s->head |-> ?head &*& nodes(head);
@*/

unsafe fn dispose_nodes(n: *mut Node)
    //@ requires nodes(n);
    //@ ensures true;
{
    if !n.is_null() {
        //@ open nodes(n);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {

    unsafe fn create() -> *mut Stack
        //@ requires true;
        //@ ensures stack(return);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(std::ptr::null_mut());
        //@ close stack(stack);
        return stack;
    }

    unsafe fn is_empty(stack: *mut Stack) -> bool
        //@ requires stack(stack);
        //@ ensures stack(stack);
    {
        let _head = (*stack).head;
        let result = (*stack).head.is_null();
        return result;
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        //@ requires stack(stack);
        //@ ensures stack(stack);
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ open stack(stack);
        //@ close nodes(n);
        //@ close stack(stack);
        (*stack).head = n;
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        //@ requires stack(stack) &*& (*stack).head != std::ptr::null_mut();
        //@ ensures stack(stack);
    {
        let head = (*stack).head;
        //@ open stack(stack);
        //@ open nodes(head);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack);
        return result;
    }

    unsafe fn dispose(stack: *mut Stack)
        //@ requires stack(stack);
        //@ ensures true;
    {
        //@ open stack(stack);
        dispose_nodes((*stack).head);
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