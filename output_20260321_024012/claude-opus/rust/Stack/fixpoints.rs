use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

/*@

predicate nodes(?n, *mut Node head) =
    head == std::ptr::null_mut() ?
        n == 0
    :
        n > 0 &*& head |-> Node { next: ?next, value: _ } &*& nodes(n - 1, next);

predicate stack(struct Stack *stack, int n) =
    stack |-> Stack { head: ?head } &*& nodes(n, head);

@*/

struct Stack {
    head: *mut Node,
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ requires true;
    //@ ensures stack(result, 0);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        //@ close stack(stack, 0);
        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ requires stack(stack, ?n);
    //@ ensures stack(stack, n + 1);
    {
        //@ open stack(stack, n);
        let nnode = alloc(Layout::new::<Node>()) as *mut Node;
        if nnode.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*nnode).next = (*stack).head;
        (*nnode).value = value;
        (*stack).head = nnode;
        //@ close nodes(n + 1, (*stack).head);
        //@ close stack(stack, n + 1);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ requires stack(stack, ?n) &*& n > 0;
    //@ ensures stack(stack, n - 1);
    {
        //@ open stack(stack, n);
        let head = (*stack).head;
        //@ open nodes(n, head);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, n - 1);
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ requires stack(stack, 0);
    //@ ensures true;
    {
        //@ open stack(stack, 0);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main()
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        let result1 = Stack::pop(s);

        let result2 = Stack::pop(s);

        Stack::dispose(s);
    }
}