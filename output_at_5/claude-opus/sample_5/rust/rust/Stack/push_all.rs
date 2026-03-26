use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@

predicate node_pred(Node *n) =
    n->next |-> ?next &*& n->value |-> _ &*&
    (next == std::ptr::null_mut() || node_pred(next));

predicate stack_pred(Stack *s) =
    s->head |-> ?head &*& (head == std::ptr::null_mut() || node_pred(head));

@*/

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ requires true;
    //@ ensures stack_pred(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack_pred(stack);
        stack
    }

    unsafe fn get_count(stack: *mut Stack) -> i32
    //@ requires stack_pred(stack);
    //@ ensures stack_pred(stack);
    {
        //@ open stack_pred(stack);
        let head = (*stack).head;
        let mut n = head;
        let mut i = 0;
        while !n.is_null()
        //@ invariant stack_pred(stack) &*& (n == std::ptr::null_mut() || node_pred(n)) &*& i >= 0;
        {
            //@ open node_pred(n);
            n = (*n).next;
            i += 1;
        }
        //@ close stack_pred(stack);
        i
    }

    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
    //@ requires stack_pred(stack) &*& stack_pred(other);
    //@ ensures stack_pred(stack);
    {
        //@ open stack_pred(stack);
        //@ open stack_pred(other);
        let head0 = (*other).head;
        //@ close stack_pred(other);
        dealloc(other as *mut u8, Layout::new::<Stack>());

        let mut n = head0;
        if !n.is_null() {
            //@ open node_pred(n);
            while !(*n).next.is_null()
            //@ invariant (n != std::ptr::null_mut() && node_pred(n));
            {
                n = (*n).next;
                //@ open node_pred(n);
            }
            (*n).next = (*stack).head;
            (*stack).head = head0;
            //@ close stack_pred(stack);
        } else {
            //@ close stack_pred(stack);
        }
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ requires stack_pred(stack);
    //@ ensures stack_pred(stack);
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ open stack_pred(stack);
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close node_pred(n);
        //@ close stack_pred(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ requires stack_pred(stack) &*& (*stack).head != std::ptr::null_mut();
    //@ ensures stack_pred(stack);
    {
        //@ open stack_pred(stack);
        let head = (*stack).head;
        //@ open node_pred(head);
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ close stack_pred(stack);
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ requires stack_pred(stack);
    //@ ensures true;
    {
        //@ open stack_pred(stack);
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